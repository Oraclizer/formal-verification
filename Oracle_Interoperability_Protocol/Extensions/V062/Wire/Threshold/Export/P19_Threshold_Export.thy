theory P19_Threshold_Export
  imports "OIP_P19_Threshold_G0.P19_Threshold_Raw_G0"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen"
begin

declare p19_votes_ok_def[code del]

lemma p19_votes_ok_executable [code]:
  "p19_votes_ok strict r message votes =
    (p19_quorum r \<le> length votes \<and> sorted_wrt (<) (map fst votes) \<and>
     (\<forall>(i,s) \<in> set votes. length s = 64 \<and> wire_octets s \<and>
       (case map_of (p19_members r) i of None \<Rightarrow> False
        | Some p19_member_key \<Rightarrow> strict p19_member_key message s)))"
proof -
  have lookup: "(\<exists>k. map_of (p19_members r) i = Some k \<and> strict k message s) =
      (case map_of (p19_members r) i of None \<Rightarrow> False
       | Some p19_member_key \<Rightarrow> strict p19_member_key message s)" for i s
    by (cases "map_of (p19_members r) i") auto
  show ?thesis by (simp add: p19_votes_ok_def lookup)
qed

type_synonym p19_export_result = "nat list \<times> wire_bytes list"
type_synonym p19_key_checks = "(wire_bytes \<times> bool) list"
type_synonym p19_strict_checks = "(wire_bytes \<times> wire_bytes \<times> wire_bytes \<times> bool) list"

definition p19_observed_key where
  "p19_observed_key checks k \<longleftrightarrow> (k,True) \<in> set checks \<and> (k,False) \<notin> set checks"

definition p19_observed_strict where
  "p19_observed_strict checks k m s \<longleftrightarrow>
    (k,m,s,True) \<in> set checks \<and> (k,m,s,False) \<notin> set checks"

lemma a_strict_observation_is_bound_to_all_three_exact_inputs:
  "p19_observed_strict checks k m s \<Longrightarrow> (k,m,s,True) \<in> set checks"
  by (simp add: p19_observed_strict_def)

definition p19_key_status :: "p19_key_checks \<Rightarrow> wire_bytes \<Rightarrow> nat" where
  "p19_key_status checks k =
    (if (k,True) \<in> set checks then (if (k,False) \<in> set checks then 3 else 0)
     else if (k,False) \<in> set checks then 1 else 2)"

definition p19_strict_status :: "p19_strict_checks \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> nat" where
  "p19_strict_status checks k m s =
    (if (k,m,s,True) \<in> set checks then (if (k,m,s,False) \<in> set checks then 3 else 0)
     else if (k,m,s,False) \<in> set checks then 1 else 2)"

fun p19_scan_keys :: "p19_key_checks \<Rightarrow> wire_bytes list \<Rightarrow> nat" where
  "p19_scan_keys checks [] = 0"
| "p19_scan_keys checks (k # rest) =
    (let status = p19_key_status checks k in if status = 0 then p19_scan_keys checks rest else status)"

fun p19_scan_votes :: "p19_strict_checks \<Rightarrow> (nat \<times> wire_bytes) list \<Rightarrow> wire_bytes \<Rightarrow> p19_votes \<Rightarrow> nat" where
  "p19_scan_votes checks members m [] = 0"
| "p19_scan_votes checks members m ((i,s) # rest) =
    (case map_of members i of None \<Rightarrow> 4 | Some k \<Rightarrow>
      let status = p19_strict_status checks k m s in
      if status = 0 then p19_scan_votes checks members m rest else status)"

lemma p19_key_scan_success:
  "p19_scan_keys checks keys = 0 \<Longrightarrow> \<forall>k \<in> set keys. p19_observed_key checks k"
  by (induction keys)
    (auto simp: p19_key_status_def p19_observed_key_def Let_def split: if_splits)

lemma p19_vote_scan_success:
  "p19_scan_votes checks members m votes = 0 \<Longrightarrow>
    \<forall>(i,s) \<in> set votes. \<exists>k. map_of members i = Some k \<and> p19_observed_strict checks k m s"
proof (induction votes)
  case Nil
  then show ?case by simp
next
  case (Cons vote votes)
  obtain i s where pair: "vote = (i,s)" by (cases vote) auto
  obtain k where key: "map_of members i = Some k"
    and status: "p19_strict_status checks k m s = 0"
    and rest: "p19_scan_votes checks members m votes = 0"
    using Cons.prems by (auto simp: pair Let_def split: option.splits if_splits)
  have first: "p19_observed_strict checks k m s"
    using status by (auto simp: p19_strict_status_def p19_observed_strict_def split: if_splits)
  show ?case using key first Cons.IH[OF rest] by (auto simp: pair)
qed

lemma p19_scan_results_supply_the_checked_predicates:
  assumes shape: "p19_roster_ok (\<lambda>_. True) r"
    and votes: "p19_votes_ok (\<lambda>_ _ _. True) r m entries"
    and keys: "p19_scan_keys key_checks (map snd (p19_members r)) = 0"
    and signatures: "p19_scan_votes strict_checks (p19_members r) m entries = 0"
  shows "p19_roster_ok (p19_observed_key key_checks) r"
    "p19_votes_ok (p19_observed_strict strict_checks) r m entries"
  using shape votes p19_key_scan_success[OF keys] p19_vote_scan_success[OF signatures]
  by (auto simp: p19_roster_ok_def p19_roster_shape_def p19_votes_ok_def)

definition p19_export_roster :: "nat list \<Rightarrow> (nat \<times> wire_bytes) list \<Rightarrow> p19_roster option" where
  "p19_export_roster header members =
    (case header of [p19_cfg_deployment,p19_cfg_source,p19_cfg_principal,p19_cfg_group,p19_cfg_epoch,p19_cfg_quorum] \<Rightarrow>
       Some \<lparr>p19_deployment = p19_cfg_deployment, p19_source = p19_cfg_source, p19_principal = p19_cfg_principal,
         p19_group_key = p19_cfg_group, p19_epoch = p19_cfg_epoch, p19_quorum = p19_cfg_quorum, p19_members = members\<rparr>
     | _ \<Rightarrow> None)"

text \<open>
  The selector is a trusted current host snapshot, supplied separately from
  both the Packet and the returned roster contents. The catalogue lookup key
  comes from this selector, not from the roster's own self-description.
  This is a one-selected-slot ABI. Registry provenance/currentness is external;
  the exact selector, roster metadata, keys and packet relation is checked here.
\<close>

definition p19_export_registry :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat \<times> wire_bytes) list \<Rightarrow> p19_registry" where
  "p19_export_registry current header members =
    (case current of [p19_cfg_deployment,p19_cfg_source,p19_cfg_principal,p19_cfg_group,p19_cfg_epoch] \<Rightarrow>
       \<lparr>p19_current_epoch = (\<lambda>slot. if slot = (p19_cfg_deployment,p19_cfg_source,p19_cfg_principal,p19_cfg_group)
          then Some p19_cfg_epoch else None),
        p19_catalogue = (\<lambda>slot. if slot = ((p19_cfg_deployment,p19_cfg_source,p19_cfg_principal,p19_cfg_group),p19_cfg_epoch)
          then p19_export_roster header members else None)\<rparr>
     | _ \<Rightarrow> \<lparr>p19_current_epoch = (\<lambda>_. None), p19_catalogue = (\<lambda>_. None)\<rparr>)"

definition p19_export_refusal :: "nat \<Rightarrow> p19_export_result" where
  "p19_export_refusal reason = ([0,reason],[])"

definition p19_export_metadata :: "nat \<Rightarrow> nat \<Rightarrow> p19_export_result" where
  "p19_export_metadata stage cause = ([3,stage,cause],[])"

definition p19_export_accept :: "p19_roster \<Rightarrow> p19_votes \<Rightarrow> wire_packet \<Rightarrow> p19_export_result" where
  "p19_export_accept r votes packet =
    ([1,p19_deployment r,p19_source r,p19_principal r,p19_group_key r,p19_epoch r,
      p19_quorum r,length votes] @ map fst votes,
      [encode_wire_core (packet_core packet),envelope_signing_bytes (packet_core packet),packet_signature packet])"

definition p19_export_step ::
  "nat \<Rightarrow> nat list \<Rightarrow> p19_registry \<Rightarrow> p19_key_checks \<Rightarrow> p19_strict_checks \<Rightarrow>
    wire_packet \<Rightarrow> p19_export_result" where
  "p19_export_step max_frame schemes registry key_checks strict_checks packet =
    (let c = packet_core packet in
     if \<not> wire_packet_wellformed packet \<or> length (encode_wire_packet packet) > max_frame
       then p19_export_refusal 70
     else if wire_signature_scheme c = 1 then ([2],[])
     else if wire_signature_scheme c \<noteq> 2 then p19_export_refusal 70
     else if 2 \<notin> set schemes then p19_export_refusal 74
     else case p19_select registry c of None \<Rightarrow> p19_export_refusal 74 | Some r \<Rightarrow>
       if \<not> p19_roster_ok (\<lambda>_. True) r then p19_export_refusal 74
       else case p19_decode_payload max_frame (length (p19_members r)) (packet_signature packet) of
         None \<Rightarrow> p19_export_refusal 74 | Some votes \<Rightarrow>
           if \<not> p19_votes_ok (\<lambda>_ _ _. True) r (envelope_signing_bytes c) votes
           then p19_export_refusal 74
           else let key_status = p19_scan_keys key_checks (map snd (p19_members r)) in
             if key_status = 1 then p19_export_refusal 74
             else if key_status \<noteq> 0 then p19_export_metadata 1 key_status
             else let strict_status = p19_scan_votes strict_checks (p19_members r) (envelope_signing_bytes c) votes in
               if strict_status = 1 then p19_export_refusal 74
               else if strict_status \<noteq> 0 then p19_export_metadata 2 strict_status
               else p19_export_accept r votes packet)"

definition p19_export_is_accept :: "p19_export_result \<Rightarrow> bool" where
  "p19_export_is_accept result \<longleftrightarrow> (case fst result of tag # rest \<Rightarrow> tag = 1 | [] \<Rightarrow> False)"

theorem p19_export_success_reuses_the_verified_threshold_contract:
  assumes "p19_export_is_accept
    (p19_export_step max_frame schemes registry key_checks strict_checks packet)"
  shows "wire_signature_scheme (packet_core packet) = 2"
    "2 \<in> set schemes"
    "length (encode_wire_packet packet) \<le> max_frame"
    "p19_threshold_ok (p19_observed_key key_checks) (p19_observed_strict strict_checks)
       registry max_frame (packet_core packet) (packet_signature packet)"
  using assms p19_scan_results_supply_the_checked_predicates
  by (auto simp: p19_export_step_def p19_export_is_accept_def p19_export_refusal_def
      p19_export_metadata_def p19_export_accept_def p19_threshold_ok_def Let_def split: option.splits if_splits)

definition p19_export_packet where
  "p19_export_packet max_frame schemes registry key_checks strict_checks bytes =
    (case code_check_declared_version bytes max_frame of
       Some reason \<Rightarrow> p19_export_refusal (code_transport_refusal_number reason)
     | None \<Rightarrow> case decode_wire_packet bytes of None \<Rightarrow> p19_export_refusal 70
       | Some packet \<Rightarrow> p19_export_step max_frame schemes registry key_checks strict_checks packet)"

definition p19_export_payload where
  "p19_export_payload max_frame schemes registry key_checks strict_checks core_bytes payload =
    (case decode_wire_core core_bytes of None \<Rightarrow> p19_export_refusal 70
     | Some c \<Rightarrow> if wire_version c \<noteq> 6 then p19_export_refusal 71
       else p19_export_step max_frame schemes registry key_checks strict_checks
         \<lparr>packet_core = c, packet_signature = payload\<rparr>)"

lemma p19_oversized_original_packet_is_format_refusal:
  "length bytes > max_frame \<Longrightarrow>
    p19_export_packet max_frame schemes registry key_checks strict_checks bytes = p19_export_refusal 70"
  by (simp add: p19_export_packet_def code_check_declared_version_def)

lemma p19_missing_and_conflicting_strict_facts_are_metadata_states:
  "(k,m,s,True) \<notin> set facts \<Longrightarrow> (k,m,s,False) \<notin> set facts \<Longrightarrow>
    p19_strict_status facts k m s = 2"
  "(k,m,s,True) \<in> set facts \<Longrightarrow> (k,m,s,False) \<in> set facts \<Longrightarrow>
    p19_strict_status facts k m s = 3"
  "(k,m,s,True) \<notin> set facts \<Longrightarrow> (k,m,s,False) \<in> set facts \<Longrightarrow>
    p19_strict_status facts k m s = 1"
  by (simp_all add: p19_strict_status_def)

lemma p19_missing_and_conflicting_key_facts_are_metadata_states:
  "(k,True) \<notin> set facts \<Longrightarrow> (k,False) \<notin> set facts \<Longrightarrow> p19_key_status facts k = 2"
  "(k,True) \<in> set facts \<Longrightarrow> (k,False) \<in> set facts \<Longrightarrow> p19_key_status facts k = 3"
  "(k,True) \<notin> set facts \<Longrightarrow> (k,False) \<in> set facts \<Longrightarrow> p19_key_status facts k = 1"
  by (simp_all add: p19_key_status_def)

lemma p19_metadata_tag_is_never_a_protocol_verdict:
  "p19_export_metadata stage cause \<noteq> p19_export_refusal code"
  by (simp add: p19_export_metadata_def p19_export_refusal_def)

lemma p19_required_strict_metadata_failure_is_not_signature_refusal:
  assumes packet: "wire_packet_wellformed packet" "length (encode_wire_packet packet) \<le> max_frame"
    and scheme: "wire_signature_scheme (packet_core packet) = 2" "2 \<in> set schemes"
    and selected: "p19_select registry (packet_core packet) = Some r"
    and roster: "p19_roster_ok (\<lambda>_. True) r"
    and decoded: "p19_decode_payload max_frame (length (p19_members r)) (packet_signature packet) = Some votes"
    and shape: "p19_votes_ok (\<lambda>_ _ _. True) r (envelope_signing_bytes (packet_core packet)) votes"
    and keys: "p19_scan_keys key_checks (map snd (p19_members r)) = 0"
    and status: "p19_scan_votes strict_checks (p19_members r) (envelope_signing_bytes (packet_core packet)) votes = cause"
    and metadata: "cause \<noteq> 0" "cause \<noteq> 1"
  shows "p19_export_step max_frame schemes registry key_checks strict_checks packet = p19_export_metadata 2 cause"
    "p19_export_step max_frame schemes registry key_checks strict_checks packet \<noteq> p19_export_refusal 74"
  using assms by (simp_all add: p19_export_step_def p19_export_metadata_def p19_export_refusal_def Let_def)

definition p19_trace_positive where
  "p19_trace_positive =
    [(replicate 32 11,envelope_signing_bytes p19_test_core,replicate 64 31,True),
     (replicate 32 22,envelope_signing_bytes p19_test_core,replicate 64 32,True)]"

definition p19_trace_missing_one where
  "p19_trace_missing_one = take 1 p19_trace_positive"

definition p19_trace_conflict where
  "p19_trace_conflict = p19_trace_positive @
    [(replicate 32 22,envelope_signing_bytes p19_test_core,replicate 64 32,False)]"

definition p19_trace_false where
  "p19_trace_false = take 1 p19_trace_positive @
    [(replicate 32 22,envelope_signing_bytes p19_test_core,replicate 64 32,False)]"

lemma p19_missing_one_and_conflict_do_not_masquerade_as_false:
  "p19_scan_votes p19_trace_positive (p19_members p19_test_roster)
    (envelope_signing_bytes p19_test_core) p19_good_votes = 0"
  "p19_scan_votes p19_trace_missing_one (p19_members p19_test_roster)
    (envelope_signing_bytes p19_test_core) p19_good_votes = 2"
  "p19_scan_votes p19_trace_conflict (p19_members p19_test_roster)
    (envelope_signing_bytes p19_test_core) p19_good_votes = 3"
  "p19_scan_votes p19_trace_false (p19_members p19_test_roster)
    (envelope_signing_bytes p19_test_core) p19_good_votes = 1"
  by (simp_all add: p19_trace_positive_def p19_trace_missing_one_def p19_trace_conflict_def
      p19_trace_false_def p19_test_roster_def p19_good_votes_def p19_strict_status_def Let_def)

definition p19_integer_nonnegative where
  "p19_integer_nonnegative xs \<longleftrightarrow> (\<forall>x \<in> set xs. 0 \<le> (x::integer))"

definition p19_integer_octets where
  "p19_integer_octets xs \<longleftrightarrow> (\<forall>x \<in> set xs. 0 \<le> (x::integer) \<and> x < 256)"

definition p19_export_integer_metadata_ok where
  "p19_export_integer_metadata_ok max_frame schemes current header members key_checks strict_checks \<longleftrightarrow>
    0 \<le> (max_frame::integer) \<and> p19_integer_nonnegative schemes \<and>
    (length current = 0 \<or> length current = 5) \<and> p19_integer_nonnegative current \<and>
    (length header = 0 \<or> length header = 6) \<and> p19_integer_nonnegative header \<and>
    (header = [] \<longrightarrow> members = []) \<and>
    (\<forall>(i,k) \<in> set members. 0 \<le> i \<and> p19_integer_octets k) \<and>
    (\<forall>(k,b) \<in> set key_checks. p19_integer_octets k) \<and>
    (\<forall>(k,m,s,b) \<in> set strict_checks.
      p19_integer_octets k \<and> p19_integer_octets m \<and> p19_integer_octets s)"

definition p19_export_integer_run where
  "p19_export_integer_run run max_frame schemes current header members key_checks strict_checks =
    (if \<not> p19_export_integer_metadata_ok max_frame schemes current header members key_checks strict_checks
     then None else
       let ns = map nat_of_integer;
           registry = p19_export_registry (ns current) (ns header) (map (\<lambda>(i,k). (nat_of_integer i,ns k)) members);
           keys = map (\<lambda>(k,b). (ns k,b)) key_checks;
           facts = map (\<lambda>(k,m,s,b). (ns k,ns m,ns s,b)) strict_checks;
           (words,blobs) = run (nat_of_integer max_frame) (ns schemes) registry keys facts
       in Some (map integer_of_nat words,map (map integer_of_nat) blobs))"

definition p19_export_integer_packet where
  "p19_export_integer_packet max_frame schemes current header members key_checks strict_checks raw =
    (if \<not> p19_integer_octets raw then None else
       p19_export_integer_run
         (\<lambda>frame selected registry keys facts.
           p19_export_packet frame selected registry keys facts (map nat_of_integer raw))
         max_frame schemes current header members key_checks strict_checks)"

definition p19_export_integer_payload where
  "p19_export_integer_payload max_frame schemes current header members key_checks strict_checks core_bytes payload =
    (if \<not> p19_integer_octets core_bytes \<or> \<not> p19_integer_octets payload then None else
       p19_export_integer_run
         (\<lambda>frame selected registry keys facts.
           p19_export_payload frame selected registry keys facts
             (map nat_of_integer core_bytes) (map nat_of_integer payload))
         max_frame schemes current header members key_checks strict_checks)"

text \<open>
  No expected verdict, parsed signer list, aggregate signature-valid flag,
  arbitrary chosen key or independent payload limit is an ABI input.
  Missing or conflicting required primitive facts return metadata tag 3, never
  a protocol verdict. A present, unambiguous False returns signature refusal.
  Primitive scans stop at the first False or metadata failure. Structural,
  membership and quorum failures precede primitive lookup. Identical true
  observations may repeat. The model derives the exact preimage from Core.
  Outer scope/TTL, attestation, operand decoding, replay mutation, persistent
  authorization and response behavior remain separate consumer obligations.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      a_strict_observation_is_bound_to_all_three_exact_inputs
      p19_export_success_reuses_the_verified_threshold_contract
      p19_oversized_original_packet_is_format_refusal
      p19_required_strict_metadata_failure_is_not_signature_refusal
      p19_missing_one_and_conflict_do_not_masquerade_as_false})
  then () else error "Unexpected oracle in threshold export ABI"
\<close>

export_code p19_export_integer_packet p19_export_integer_payload
  in SML module_name OIP_P19_Threshold_ABI file_prefix "oip_p19_threshold_abi"

end
