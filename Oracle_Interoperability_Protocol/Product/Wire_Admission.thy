theory Wire_Admission
  imports Wire_Negotiation
begin

record wire_boundary =
  boundary_profile :: negotiated_wire_profile
  boundary_deployment :: nat
  boundary_source :: nat
  boundary_target :: nat
  boundary_principal :: nat
  boundary_key :: nat
  boundary_epoch :: nat
  boundary_route_scope :: nat
  boundary_now :: nat
  boundary_asset_ttl_floor :: nat
  boundary_future_skew :: nat
  boundary_max_frame :: nat
  boundary_version_floor :: nat
  boundary_critical_allowed :: bool
  boundary_threshold_supported :: bool

datatype wire_refusal =
    Invalid_Wire_Format | Unsupported_Wire_Version | Invalid_Wire_Source | Invalid_Wire_Signature
  | Invalid_Wire_Threshold | Wire_TTL_Expired | Wire_TTL_Invalid | Conflicting_Wire_Replay

datatype wire_gate_result = Gate_Admitted wire_packet | Gate_Refused wire_refusal

definition current_wire_scope where
  "current_wire_scope authority core \<longleftrightarrow>
    wire_deployment core = boundary_deployment authority \<and>
    wire_source_domain core = boundary_source authority \<and> wire_target_domain core = boundary_target authority \<and>
    wire_principal core = boundary_principal authority \<and> wire_key_number core = boundary_key authority \<and>
    wire_authority_epoch core = boundary_epoch authority \<and> wire_route_scope core = boundary_route_scope authority \<and> wire_purpose core = 1 \<and>
    (wire_priority core = 0 \<longrightarrow> boundary_critical_allowed authority)"

definition effective_wire_ttl where
  "effective_wire_ttl authority core = max (wire_ttl_seconds core) (boundary_asset_ttl_floor authority)"

definition wire_expiry where
  "wire_expiry authority core = wire_sent_seconds core + effective_wire_ttl authority core"

definition wire_gate where
  "wire_gate verify attest body_allowed authority bytes =
    (if length bytes > boundary_max_frame authority then Gate_Refused Invalid_Wire_Format
     else case decode_wire_packet bytes of None \<Rightarrow> Gate_Refused Invalid_Wire_Format | Some packet \<Rightarrow>
       let core = packet_core packet; profile = boundary_profile authority in
       if negotiated_version profile \<noteq> 6 \<or> wire_version core \<noteq> 6 \<or> boundary_version_floor authority > 6 \<or>
          wire_message_family core \<notin> negotiated_families profile \<or> wire_atomicity core \<notin> negotiated_atomicities profile
       then Gate_Refused Unsupported_Wire_Version
       else if \<not> current_wire_scope authority core then Gate_Refused Invalid_Wire_Source
       else if wire_expiry authority core \<ge> 2^64 \<or> boundary_now authority + boundary_future_skew authority \<ge> 2^64 \<or>
           wire_sent_seconds core > boundary_now authority + boundary_future_skew authority
       then Gate_Refused Wire_TTL_Invalid
       else if wire_expiry authority core < boundary_now authority then Gate_Refused Wire_TTL_Expired
       else if wire_signature_scheme core \<notin> negotiated_schemes profile \<or>
           (wire_signature_scheme core = 2 \<and> \<not> boundary_threshold_supported authority) \<or>
           \<not> verify core (envelope_signing_bytes core) (packet_signature packet)
       then Gate_Refused (if wire_signature_scheme core = 2 then Invalid_Wire_Threshold else Invalid_Wire_Signature)
       else if \<not> attest core then Gate_Refused Invalid_Wire_Source
       else if \<not> body_allowed profile core then Gate_Refused Invalid_Wire_Format
       else Gate_Admitted packet)"

lemma a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature:
  assumes "wire_gate verify attest body_allowed authority bytes = Gate_Admitted packet"
  shows "decode_wire_packet bytes = Some packet \<and> current_wire_scope authority (packet_core packet) \<and>
    verify (packet_core packet) (envelope_signing_bytes (packet_core packet)) (packet_signature packet) \<and>
    attest (packet_core packet) \<and> body_allowed (boundary_profile authority) (packet_core packet) \<and>
    boundary_now authority \<le> wire_expiry authority (packet_core packet)"
  using assms by (auto simp: wire_gate_def Let_def split: option.splits if_splits)

type_synonym authenticated_message_id = "nat \<times> nat \<times> nat \<times> wire_bytes"
type_synonym wire_dedup_store = "authenticated_message_id \<Rightarrow> wire_bytes option"

definition authenticated_wire_message_id where
  "authenticated_wire_message_id core = (wire_deployment core, wire_source_domain core, wire_principal core, wire_uuid core)"

datatype wire_receive_result =
    Wire_First wire_packet | Wire_Identical wire_packet | Wire_Rejected wire_refusal

definition receive_canonical_wire where
  "receive_canonical_wire verify attest body_allowed authority bytes cache =
    (case wire_gate verify attest body_allowed authority bytes of
       Gate_Refused reason \<Rightarrow> (cache, Wire_Rejected reason)
     | Gate_Admitted packet \<Rightarrow> let core = packet_core packet; key = authenticated_wire_message_id core;
                                  exact = encode_wire_core core in
         case cache key of None \<Rightarrow> (cache(key := Some exact), Wire_First packet)
          | Some prior \<Rightarrow> if prior = exact then (cache, Wire_Identical packet)
            else (cache, Wire_Rejected Conflicting_Wire_Replay))"

theorem deduplication_changes_only_after_the_original_canonical_signature_and_identity:
  assumes "fst (receive_canonical_wire verify attest body_allowed authority bytes cache) \<noteq> cache"
  shows "\<exists>packet. wire_gate verify attest body_allowed authority bytes = Gate_Admitted packet \<and>
     verify (packet_core packet) (envelope_signing_bytes (packet_core packet)) (packet_signature packet) \<and> attest (packet_core packet)"
proof -
  obtain packet where admitted: "wire_gate verify attest body_allowed authority bytes = Gate_Admitted packet"
    using assms by (cases "wire_gate verify attest body_allowed authority bytes")
      (auto simp: receive_canonical_wire_def)
  show ?thesis using admitted a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature[OF admitted] by blast
qed

lemma the_same_uuid_with_changed_signed_fields_cannot_replace_the_retained_body:
  assumes admitted: "wire_gate verify attest body_allowed authority bytes = Gate_Admitted packet"
    and old: "cache (authenticated_wire_message_id (packet_core packet)) = Some prior"
    and change: "prior \<noteq> encode_wire_core (packet_core packet)"
  shows "receive_canonical_wire verify attest body_allowed authority bytes cache =
    (cache, Wire_Rejected Conflicting_Wire_Replay)"
  using assms by (simp add: receive_canonical_wire_def Let_def)

lemma an_expired_envelope_cannot_use_a_retained_uuid:
  assumes "decode_wire_packet bytes = Some packet"
    "wire_expiry authority (packet_core packet) < boundary_now authority"
  shows "\<exists>reason. receive_canonical_wire verify attest body_allowed authority bytes cache = (cache, Wire_Rejected reason)"
  using assms by (auto simp: wire_gate_def receive_canonical_wire_def Let_def split: if_splits)

end
