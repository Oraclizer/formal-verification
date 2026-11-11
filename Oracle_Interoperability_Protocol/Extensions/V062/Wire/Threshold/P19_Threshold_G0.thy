theory P19_Threshold_G0
  imports "OIP_Message_Code.Wire_Code_Admission"
begin

text \<open>
  Isolated G0 candidate. No build or proof credit is claimed for this source.
  The existing canonical packet, Core, signing preimage, scope/TTL gate and
  transport key are imported. This candidate supplies only the new threshold
  payload and exact-current-registry selector. It is not a Rust/Go refinement.
\<close>

type_synonym p19_votes = "(nat \<times> wire_bytes) list"
type_synonym p19_slot = "nat \<times> nat \<times> nat \<times> nat"
type_synonym p19_strict = "wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool"

record p19_roster =
  p19_deployment :: nat
  p19_source :: nat
  p19_principal :: nat
  p19_group_key :: nat
  p19_epoch :: nat
  p19_quorum :: nat
  p19_members :: "(nat \<times> wire_bytes) list"

record p19_registry =
  p19_current_epoch :: "p19_slot \<Rightarrow> nat option"
  p19_catalogue :: "(p19_slot \<times> nat) \<Rightarrow> p19_roster option"

abbreviation p19_word where "p19_word n \<equiv> rev (put_le_octets 8 n)"
abbreviation p19_read_word where
  "p19_read_word raw \<equiv> get_le_octets (rev (take 8 raw))"

definition p19_core_slot :: "wire_core \<Rightarrow> p19_slot" where
  "p19_core_slot c = (wire_deployment c, wire_source_domain c,
     wire_principal c, wire_key_number c)"

definition p19_matches_core where
  "p19_matches_core r c \<longleftrightarrow>
    p19_deployment r = wire_deployment c \<and> p19_source r = wire_source_domain c \<and>
    p19_principal r = wire_principal c \<and> p19_group_key r = wire_key_number c \<and>
    p19_epoch r = wire_authority_epoch c"

definition p19_select where
  "p19_select registry c =
    (if p19_current_epoch registry (p19_core_slot c) = Some (wire_authority_epoch c)
     then (case p19_catalogue registry (p19_core_slot c, wire_authority_epoch c) of
       None \<Rightarrow> None | Some r \<Rightarrow> if p19_matches_core r c then Some r else None)
     else None)"

lemma selected_roster_is_current_and_exact:
  assumes "p19_select registry c = Some r"
  shows "p19_current_epoch registry (p19_core_slot c) = Some (wire_authority_epoch c)"
    "p19_catalogue registry (p19_core_slot c, wire_authority_epoch c) = Some r"
    "p19_matches_core r c"
  using assms by (auto simp: p19_select_def split: option.splits if_splits)

definition p19_roster_shape where
  "p19_roster_shape key_ok r \<longleftrightarrow>
    0 < p19_quorum r \<and> p19_quorum r \<le> length (p19_members r) \<and>
    distinct (map fst (p19_members r)) \<and>
    (\<forall>(i,k) \<in> set (p19_members r). i < 2^64 \<and>
       length k = 32 \<and> wire_octets k \<and> key_ok k)"

definition p19_no_key_alias where
  "p19_no_key_alias r \<longleftrightarrow> distinct (map snd (p19_members r))"

definition p19_roster_ok where
  "p19_roster_ok key_ok r \<longleftrightarrow>
    p19_roster_shape key_ok r \<and> p19_no_key_alias r"

definition p19_payload_bytes where
  "p19_payload_bytes votes = p19_word (length votes) @
    concat (map (\<lambda>(i,s). p19_word i @ s) votes)"

fun p19_parse_records :: "nat \<Rightarrow> wire_bytes \<Rightarrow> p19_votes" where
  "p19_parse_records 0 raw = []"
| "p19_parse_records (Suc n) raw =
    (p19_read_word raw, take 64 (drop 8 raw)) # p19_parse_records n (drop 72 raw)"

lemma p19_parsed_count [simp]: "length (p19_parse_records n raw) = n"
  by (induction n arbitrary: raw) simp_all

definition p19_decode_payload where
  "p19_decode_payload max_signature roster_size raw =
    (if \<not> wire_octets raw \<or> length raw < 8 \<or> length raw > max_signature then None
     else let n = p19_read_word raw in
       if n \<ge> 2^64 \<or> n > roster_size \<or> n > (length raw - 8) div 72 \<or>
          length raw \<noteq> 8 + 72 * n then None
       else Some (p19_parse_records n (drop 8 raw)))"

text \<open>
  HOL naturals do not wrap. The source consumer must compare the count with
  (length - 8) div 72 and the installed roster size before multiplication,
  conversion, allocation, iteration or curve verification. A source-sized
  integer simulation remains a separate Rust/Go obligation.
\<close>

lemma decoded_payload_has_exact_count_and_both_bounds:
  assumes "p19_decode_payload cap members raw = Some votes"
  shows "length raw = 8 + 72 * length votes"
    "length raw \<le> cap" "length votes \<le> members"
    "length votes < 2^64" "wire_octets raw"
  using assms
  by (auto simp: p19_decode_payload_def Let_def split: if_splits)

lemma a_truncated_or_trailing_record_is_not_decoded:
  assumes "8 \<le> length raw" "length raw \<noteq> 8 + 72 * p19_read_word raw"
  shows "p19_decode_payload cap members raw = None"
  using assms by (simp add: p19_decode_payload_def Let_def)

definition p19_votes_ok where
  "p19_votes_ok strict r message votes \<longleftrightarrow>
    p19_quorum r \<le> length votes \<and> sorted_wrt (<) (map fst votes) \<and>
    (\<forall>(i,s) \<in> set votes. length s = 64 \<and> wire_octets s \<and>
       (\<exists>k. map_of (p19_members r) i = Some k \<and> strict k message s))"

definition p19_threshold_ok where
  "p19_threshold_ok key_ok strict registry cap c raw \<longleftrightarrow>
    (case p19_select registry c of None \<Rightarrow> False | Some r \<Rightarrow>
       p19_roster_ok key_ok r \<and>
       (case p19_decode_payload cap (length (p19_members r)) raw of
         None \<Rightarrow> False | Some votes \<Rightarrow>
           p19_votes_ok strict r (envelope_signing_bytes c) votes))"

theorem threshold_acceptance_exposes_exact_current_roster_and_signatures:
  assumes "p19_threshold_ok key_ok strict registry cap c raw"
  obtains r votes where
    "p19_select registry c = Some r"
    "p19_roster_ok key_ok r"
    "p19_decode_payload cap (length (p19_members r)) raw = Some votes"
    "0 < p19_quorum r" "p19_quorum r \<le> length votes"
    "sorted_wrt (<) (map fst votes)"
    "distinct (map snd (p19_members r))"
    "\<forall>(i,s) \<in> set votes. \<exists>k.
       map_of (p19_members r) i = Some k \<and>
       strict k (envelope_signing_bytes c) s"
proof -
  obtain r votes where selected: "p19_select registry c = Some r"
    and roster: "p19_roster_ok key_ok r"
    and decoded: "p19_decode_payload cap (length (p19_members r)) raw = Some votes"
    and checked: "p19_votes_ok strict r (envelope_signing_bytes c) votes"
    using assms by (auto simp: p19_threshold_ok_def split: option.splits)
  have positive: "0 < p19_quorum r"
    using roster by (simp add: p19_roster_ok_def p19_roster_shape_def)
  have quorum: "p19_quorum r \<le> length votes"
    and ordered: "sorted_wrt (<) (map fst votes)"
    and signatures: "\<forall>(i,s) \<in> set votes. \<exists>k.
      map_of (p19_members r) i = Some k \<and> strict k (envelope_signing_bytes c) s"
    using checked by (auto simp: p19_votes_ok_def)
  have keys: "distinct (map snd (p19_members r))"
    using roster by (simp add: p19_roster_ok_def p19_no_key_alias_def)
  show thesis by (rule that[OF selected roster decoded positive quorum ordered keys signatures])
qed

locale p19_conditional_strict =
  fixes strict :: p19_strict
    and canonical_key :: "wire_bytes \<Rightarrow> bool"
    and authentic :: p19_strict
  assumes strict_sound: "strict k m s \<Longrightarrow> authentic k m s"
    and strict_key_is_canonical: "strict k m s \<Longrightarrow> canonical_key k"
begin

theorem accepted_threshold_authentication_is_conditional_on_exact_strict_inputs:
  assumes accepted: "p19_threshold_ok canonical_key strict registry cap c raw"
  obtains r votes where
    "p19_select registry c = Some r" "p19_matches_core r c"
    "p19_current_epoch registry (p19_core_slot c) = Some (wire_authority_epoch c)"
    "p19_decode_payload cap (length (p19_members r)) raw = Some votes"
    "0 < p19_quorum r" "p19_quorum r \<le> length votes"
    "sorted_wrt (<) (map fst votes)" "p19_no_key_alias r"
    "\<forall>(i,s) \<in> set votes. \<exists>k. map_of (p19_members r) i = Some k \<and>
      canonical_key k \<and> authentic k (envelope_signing_bytes c) s"
proof -
  obtain r votes where selected: "p19_select registry c = Some r"
    and roster: "p19_roster_ok canonical_key r"
    and decoded: "p19_decode_payload cap (length (p19_members r)) raw = Some votes"
    and positive: "0 < p19_quorum r"
    and quorum: "p19_quorum r \<le> length votes"
    and ordered: "sorted_wrt (<) (map fst votes)"
    and keys: "distinct (map snd (p19_members r))"
    and signatures: "\<forall>(i,s) \<in> set votes. \<exists>k.
      map_of (p19_members r) i = Some k \<and> strict k (envelope_signing_bytes c) s"
    using threshold_acceptance_exposes_exact_current_roster_and_signatures[OF accepted] by blast
  have current: "p19_current_epoch registry (p19_core_slot c) = Some (wire_authority_epoch c)"
    and exact: "p19_matches_core r c"
    using selected_roster_is_current_and_exact[OF selected] by blast+
  have no_alias: "p19_no_key_alias r" using keys by (simp add: p19_no_key_alias_def)
  have sound_each: "\<exists>k. map_of (p19_members r) i = Some k \<and>
      canonical_key k \<and> authentic k (envelope_signing_bytes c) s"
    if member: "(i,s) \<in> set votes" for i s
  proof -
    obtain k where key: "map_of (p19_members r) i = Some k"
      and strict: "strict k (envelope_signing_bytes c) s"
      using signatures member by auto
    show ?thesis using key strict_sound[OF strict] strict_key_is_canonical[OF strict] by blast
  qed
  have sound_all: "\<forall>(i,s) \<in> set votes. \<exists>k.
      map_of (p19_members r) i = Some k \<and>
      canonical_key k \<and> authentic k (envelope_signing_bytes c) s"
    using sound_each by auto
  show thesis by (rule that[OF selected exact current decoded positive quorum ordered no_alias sound_all])
qed

end

text \<open>
  Strict soundness is an external cryptographic premise, including the
  canonical/non-small-order A and R, reduced S and uncofactored equation.
  Registry provenance and the claim that this registry is current are trusted
  host inputs. Neither signer honesty nor truth of an application claim follows.
\<close>

definition p19_admit_packet where
  "p19_admit_packet single key_ok strict registry cap packet authority =
    (case code_check_versioned_scope (packet_core packet) authority 6 of
       Some reason \<Rightarrow> Some reason
     | None \<Rightarrow> let c = packet_core packet in
       if wire_signature_scheme c = 2 then
         (if 2 \<in> negotiated_schemes (boundary_profile authority) \<and>
             p19_threshold_ok key_ok strict registry cap c (packet_signature packet)
          then None else Some Invalid_Wire_Threshold)
       else if wire_signature_scheme c \<notin> negotiated_schemes (boundary_profile authority) \<or>
         \<not> single c (envelope_signing_bytes c) (packet_signature packet)
       then Some Invalid_Wire_Signature else None)"

lemma scope_or_time_failure_precedes_any_threshold_work:
  "code_check_versioned_scope (packet_core packet) authority 6 = Some reason \<Longrightarrow>
   p19_admit_packet single key_ok strict registry cap packet authority = Some reason"
  by (simp add: p19_admit_packet_def)

lemma threshold_never_uses_a_single_fallback:
  assumes "wire_signature_scheme (packet_core packet) = 2"
  shows "p19_admit_packet first key_ok strict registry cap packet authority =
         p19_admit_packet second key_ok strict registry cap packet authority"
  using assms
  by (simp add: p19_admit_packet_def Let_def split: option.splits)

lemma selected_scheme_failure_is_threshold_refusal:
  assumes "code_check_versioned_scope (packet_core packet) authority 6 = None"
    "wire_signature_scheme (packet_core packet) = 2"
    "2 \<notin> negotiated_schemes (boundary_profile authority)"
  shows "p19_admit_packet single key_ok strict registry cap packet authority = Some Invalid_Wire_Threshold"
  using assms by (simp add: p19_admit_packet_def Let_def)

lemma valid_single_path_is_unchanged:
  assumes "wire_signature_scheme (packet_core packet) = 1"
  shows "p19_admit_packet single key_ok strict registry cap packet authority =
         code_admit_packet single packet authority"
  using assms by (simp add: p19_admit_packet_def code_admit_packet_def Let_def split: option.splits)

definition p19_decoded_gate where
  "p19_decoded_gate single key_ok strict registry cap attest body_allowed authority bytes =
    (if length bytes > boundary_max_frame authority then Gate_Refused Invalid_Wire_Format
     else case decode_wire_packet bytes of None \<Rightarrow> Gate_Refused Invalid_Wire_Format
     | Some packet \<Rightarrow>
       (case p19_admit_packet single key_ok strict registry cap packet authority of
         Some reason \<Rightarrow> Gate_Refused reason
       | None \<Rightarrow> if \<not> attest (packet_core packet) then Gate_Refused Invalid_Wire_Source
         else if \<not> body_allowed (boundary_profile authority) (packet_core packet)
         then Gate_Refused Invalid_Wire_Format else Gate_Admitted packet))"

definition p19_library_gate where
  "p19_library_gate single key_ok strict registry cap attest body_allowed authority bytes =
    (if negotiated_version (boundary_profile authority) \<noteq> 6 then Gate_Refused Unsupported_Wire_Version
     else case code_check_declared_version bytes (boundary_max_frame authority) of
       Some reason \<Rightarrow> Gate_Refused reason
     | None \<Rightarrow> p19_decoded_gate single key_ok strict registry cap attest body_allowed authority bytes)"

lemma malformed_canonical_packet_is_rejected_before_threshold:
  assumes "negotiated_version (boundary_profile authority) = 6"
    "code_check_declared_version bytes (boundary_max_frame authority) = None"
    "decode_wire_packet bytes = None"
  shows "p19_library_gate single key_ok strict registry cap attest body_allowed authority bytes =
    Gate_Refused Invalid_Wire_Format"
  using assms by (simp add: p19_library_gate_def p19_decoded_gate_def)

definition p19_receive where
  "p19_receive single key_ok strict registry cap attest body_allowed authority bytes cache =
    (case p19_library_gate single key_ok strict registry cap attest body_allowed authority bytes of
       Gate_Refused reason \<Rightarrow> (cache, Wire_Rejected reason)
     | Gate_Admitted packet \<Rightarrow>
       let c = packet_core packet; key = authenticated_wire_message_id c; exact = encode_wire_core c in
       case cache key of None \<Rightarrow> (cache(key := Some exact), Wire_First packet)
       | Some old \<Rightarrow> if old = exact then (cache, Wire_Identical packet)
         else (cache, Wire_Rejected Conflicting_Wire_Replay))"

lemma invalid_threshold_does_not_reserve_a_transport_key:
  assumes "p19_library_gate single key_ok strict registry cap attest body_allowed authority bytes =
    Gate_Refused Invalid_Wire_Threshold"
  shows "p19_receive single key_ok strict registry cap attest body_allowed authority bytes cache =
    (cache, Wire_Rejected Invalid_Wire_Threshold)"
  using assms by (simp add: p19_receive_def)

lemma an_identical_retained_core_still_requires_current_admission:
  assumes "p19_library_gate single key_ok strict registry cap attest body_allowed authority bytes =
    Gate_Refused reason"
  shows "p19_receive single key_ok strict registry cap attest body_allowed authority bytes cache =
    (cache, Wire_Rejected reason)"
  using assms by (simp add: p19_receive_def)

section \<open>Smallest key-alias counterexample, before expensive curve work\<close>

definition p19_test_core :: wire_core where
  "p19_test_core = \<lparr>wire_version = 6, wire_purpose = 1, wire_deployment = 1,
    wire_source_domain = 2, wire_target_domain = 3, wire_principal = 4,
    wire_key_number = 5, wire_authority_epoch = 6, wire_sent_seconds = 100,
    wire_ttl_seconds = 10, wire_uuid = [0,0,0,0,0,0,64,0,128,0,0,0,0,0,0,1],
    wire_message_family = Wire_Query, wire_primary_code = 1, wire_secondary_code = None,
    wire_signature_scheme = 2, wire_operation_body = \<lparr>wire_opcode = 1,
      wire_words = [9,0,1,11], wire_blobs = [], wire_deadline = Deadline_Absent\<rparr>,
    wire_atomicity = 1, wire_priority = 3, wire_route_scope = 7\<rparr>"

definition p19_test_roster :: p19_roster where
  "p19_test_roster = \<lparr>p19_deployment = 1, p19_source = 2, p19_principal = 4,
    p19_group_key = 5, p19_epoch = 6, p19_quorum = 2,
    p19_members = [(1,replicate 32 11),(2,replicate 32 22)]\<rparr>"

definition p19_alias_roster where
  "p19_alias_roster = p19_test_roster\<lparr>p19_members :=
    [(1,replicate 32 11),(2,replicate 32 11)]\<rparr>"

definition p19_test_registry where
  "p19_test_registry r = \<lparr>
    p19_current_epoch = (\<lambda>slot. if slot = (1,2,4,5) then Some 6 else None),
    p19_catalogue = (\<lambda>slot. if slot = ((1,2,4,5),6) then Some r else None)\<rparr>"

definition p19_symbolic_strict :: p19_strict where
  "p19_symbolic_strict k m s \<longleftrightarrow> m = envelope_signing_bytes p19_test_core \<and>
    ((k = replicate 32 11 \<and> s = replicate 64 31) \<or>
     (k = replicate 32 22 \<and> s = replicate 64 32))"

definition p19_good_votes :: p19_votes where
  "p19_good_votes = [(1,replicate 64 31),(2,replicate 64 32)]"

definition p19_alias_votes :: p19_votes where
  "p19_alias_votes = [(1,replicate 64 31),(2,replicate 64 31)]"

text \<open>
  These are algebraic authentication witnesses, not Ed25519 signatures.
  key_ok=True and symbolic_strict are explicit finite fixtures. The source
  curve test must replace both with strict Ed25519 and frozen public test keys.
\<close>

lemma p19_positive_selected_roster:
  "p19_select (p19_test_registry p19_test_roster) p19_test_core = Some p19_test_roster"
  by (simp add: p19_select_def p19_test_registry_def p19_core_slot_def
      p19_matches_core_def p19_test_core_def p19_test_roster_def)

lemma p19_distinct_key_positive:
  "p19_roster_ok (\<lambda>_. True) p19_test_roster"
  "p19_votes_ok p19_symbolic_strict p19_test_roster
     (envelope_signing_bytes p19_test_core) p19_good_votes"
  by (simp_all add: p19_roster_ok_def p19_roster_shape_def p19_no_key_alias_def
      p19_test_roster_def p19_good_votes_def p19_votes_ok_def p19_symbolic_strict_def wire_octets_def)

lemma p19_key_alias_removal_counterexample:
  "p19_roster_shape (\<lambda>_. True) p19_alias_roster"
  "p19_votes_ok p19_symbolic_strict p19_alias_roster
      (envelope_signing_bytes p19_test_core) p19_alias_votes"
  "\<not> p19_roster_ok (\<lambda>_. True) p19_alias_roster"
  by (simp_all add: p19_roster_shape_def p19_roster_ok_def p19_no_key_alias_def
      p19_test_roster_def p19_alias_roster_def p19_alias_votes_def
      p19_votes_ok_def p19_symbolic_strict_def wire_octets_def)

lemma p19_duplicate_id_is_refused:
  "\<not> p19_votes_ok strict p19_test_roster m [(1,s),(1,t)]"
  by (simp add: p19_votes_ok_def)

lemma p19_insufficient_quorum_is_refused:
  "\<not> p19_votes_ok strict p19_test_roster m [(1,s)]"
  by (simp add: p19_votes_ok_def p19_test_roster_def)

lemma p19_changed_preimage_is_refused:
  assumes "m \<noteq> envelope_signing_bytes p19_test_core"
  shows "\<not> p19_votes_ok p19_symbolic_strict p19_test_roster m p19_good_votes"
  using assms by (auto simp: p19_votes_ok_def p19_good_votes_def
      p19_symbolic_strict_def p19_test_roster_def)

lemma p19_old_current_pointer_is_not_selected:
  assumes "p19_current_epoch registry (p19_core_slot c) \<noteq> Some (wire_authority_epoch c)"
  shows "p19_select registry c = None"
  using assms by (simp add: p19_select_def)

lemma p19_wrong_principal_roster_is_not_selected:
  assumes "p19_catalogue registry (p19_core_slot c, wire_authority_epoch c) = Some r"
    "p19_principal r \<noteq> wire_principal c"
  shows "p19_select registry c = None"
  using assms by (simp add: p19_select_def p19_matches_core_def)

lemma p19_wrong_group_key_roster_is_not_selected:
  assumes "p19_catalogue registry (p19_core_slot c, wire_authority_epoch c) = Some r"
    "p19_group_key r \<noteq> wire_key_number c"
  shows "p19_select registry c = None"
  using assms by (simp add: p19_select_def p19_matches_core_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      selected_roster_is_current_and_exact
      decoded_payload_has_exact_count_and_both_bounds
      threshold_acceptance_exposes_exact_current_roster_and_signatures
      p19_conditional_strict.accepted_threshold_authentication_is_conditional_on_exact_strict_inputs
      threshold_never_uses_a_single_fallback
      valid_single_path_is_unchanged
      p19_key_alias_removal_counterexample})
  then () else error "Unexpected oracle in threshold G0 candidate"
\<close>

end
