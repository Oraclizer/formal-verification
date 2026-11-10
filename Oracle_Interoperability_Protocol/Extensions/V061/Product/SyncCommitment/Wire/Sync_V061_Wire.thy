theory Sync_V061_Wire
  imports "OIP_Message_Code.Wire_Code_Admission"
begin

datatype sync_specification = Sync_V060 | Sync_V061

definition sync_operation where
  "sync_operation core = (wire_message_family core, wire_opcode (wire_operation_body core))"

definition sync_added_operation where
  "sync_added_operation core \<longleftrightarrow> sync_operation core \<in> {(Wire_State_Sync,7),(Wire_Query,9)}"

lemma sync_added_operation_is_outside_the_previous_family:
  "sync_added_operation core \<Longrightarrow>
    \<not> valid_family_opcode (wire_message_family core) (wire_opcode (wire_operation_body core))"
  by (auto simp: sync_added_operation_def sync_operation_def)

text \<open>The temporary legacy opcode is confined to header and body framing validation.
  The decoder restores the original body before the exact Core comparison.\<close>

fun sync_new_body_field :: "proto_field \<Rightarrow> (nat \<times> wire_body) option" where
  "sync_new_body_field (Proto_Bytes tag raw) =
    (if tag \<in> {16,19} then
       Option.bind (decode_wire_body raw) (\<lambda>body.
         if (tag, wire_opcode body) \<in> {(16,7),(19,9)} then Some (tag,body) else None)
     else None)"
| "sync_new_body_field _ = None"

definition sync_parse_new_core where
  "sync_parse_new_core wire_items =
    Option.bind (List.find (\<lambda>field. sync_new_body_field field \<noteq> None) wire_items) (\<lambda>candidate.
      Option.bind (sync_new_body_field candidate) (\<lambda>(tag,body).
        let alias = Proto_Bytes tag (encode_wire_body (body\<lparr>wire_opcode := 1\<rparr>)) in
        Option.bind (parse_core_fields (map (\<lambda>field. if field = candidate then alias else field) wire_items)) (\<lambda>legacy.
          let original = legacy\<lparr>wire_operation_body := body\<rparr> in
          if wire_core_wellformed legacy \<and> sync_added_operation original then Some original else None)))"

definition sync_decode_core where
  "sync_decode_core raw =
    (case decode_wire_core raw of Some legacy \<Rightarrow> Some legacy
     | None \<Rightarrow> Option.bind (read_canonical_proto_fields raw) (\<lambda>wire_items.
       Option.bind (sync_parse_new_core wire_items) (\<lambda>core.
         if encode_wire_core core = raw then Some core else None)))"

definition sync_decode_packet where
  "sync_decode_packet raw =
    (case decode_wire_packet raw of Some legacy \<Rightarrow> Some legacy
     | None \<Rightarrow> case read_canonical_proto_fields raw of
         Some [Proto_Bytes core_tag original, Proto_Bytes signature_tag signature] \<Rightarrow>
          if core_tag = 1 \<and> signature_tag = 2 then
            Option.bind (sync_decode_core original) (\<lambda>core.
              let packet = \<lparr>packet_core = core, packet_signature = signature\<rparr> in
              if sync_added_operation core \<and> length original < 256^4 \<and> wire_octets signature \<and>
                 (if wire_signature_scheme core = 1 then length signature = 64 else signature \<noteq> []) \<and>
                 encode_wire_packet packet = raw
              then Some packet else None)
          else None
       | _ \<Rightarrow> None)"

lemma sync_preserves_every_decoded_legacy_core:
  "decode_wire_core raw = Some core \<Longrightarrow> sync_decode_core raw = Some core"
  by (simp add: sync_decode_core_def)

lemma sync_preserves_every_decoded_legacy_packet:
  "decode_wire_packet raw = Some packet \<Longrightarrow> sync_decode_packet raw = Some packet"
  by (simp add: sync_decode_packet_def)

lemma sync_decoded_core_has_the_exact_bytes:
  assumes "sync_decode_core raw = Some core"
  shows "encode_wire_core core = raw"
  using assms accepted_core_bytes_preserve_all_original_fields
  by (auto simp: sync_decode_core_def bind_eq_Some_conv split: option.splits if_splits)

lemma sync_decoded_packet_has_the_exact_bytes:
  assumes "sync_decode_packet raw = Some packet"
  shows "encode_wire_packet packet = raw"
  using assms every_accepted_wire_message_has_exactly_the_received_bytes
  by (auto simp: sync_decode_packet_def Let_def bind_eq_Some_conv split: option.splits list.splits proto_field.splits if_splits)

lemma sync_old_decoder_refuses_a_new_recognized_packet:
  assumes "sync_decode_packet raw = Some packet" "sync_added_operation (packet_core packet)"
  shows "decode_wire_packet raw = None"
proof (cases "decode_wire_packet raw")
  case None
  then show ?thesis .
next
  case (Some legacy)
  have exact: "legacy = packet" using assms(1) Some by (simp add: sync_decode_packet_def)
  have "valid_family_opcode (wire_message_family (packet_core packet))
      (wire_opcode (wire_operation_body (packet_core packet)))"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF Some] exact
    by (simp add: wire_packet_wellformed_def wire_core_wellformed_def)
  then show ?thesis using sync_added_operation_is_outside_the_previous_family[OF assms(2)] by contradiction
qed

fun sync_packet_for :: "sync_specification \<Rightarrow> wire_bytes \<Rightarrow> wire_packet option" where
  "sync_packet_for Sync_V060 raw = decode_wire_packet raw"
| "sync_packet_for Sync_V061 raw = sync_decode_packet raw"

definition sync_send_allowed where
  "sync_send_allowed peer_accepted core \<longleftrightarrow> sync_operation core \<in> peer_accepted"

definition sync_admit_decoded where
  "sync_admit_decoded accepted verify authenticate body_allowed authority packet =
    (let core = packet_core packet in
     if sync_operation core \<notin> accepted then Gate_Refused Unsupported_Wire_Version
     else case code_admit_packet verify packet authority of Some reason \<Rightarrow> Gate_Refused reason
       | None \<Rightarrow> if \<not> authenticate core then Gate_Refused Invalid_Wire_Source
         else if \<not> body_allowed (boundary_profile authority) core then Gate_Refused Invalid_Wire_Format
         else Gate_Admitted packet)"

definition sync_v6_gate where
  "sync_v6_gate specification accepted verify authenticate body_allowed authority raw =
    (if negotiated_version (boundary_profile authority) \<noteq> 6 then Gate_Refused Unsupported_Wire_Version
     else case code_check_declared_version raw (boundary_max_frame authority) of
       Some reason \<Rightarrow> Gate_Refused reason
     | None \<Rightarrow> if length raw > boundary_max_frame authority then Gate_Refused Invalid_Wire_Format
       else case sync_packet_for specification raw of
         None \<Rightarrow> Gate_Refused Invalid_Wire_Format
       | Some packet \<Rightarrow> sync_admit_decoded accepted verify authenticate body_allowed authority packet)"

lemma sync_unconfigured_operation_stops_before_transport_checks:
  "sync_operation (packet_core packet) \<notin> accepted \<Longrightarrow>
    sync_admit_decoded accepted verify authenticate body_allowed authority packet =
      Gate_Refused Unsupported_Wire_Version"
  by (simp add: sync_admit_decoded_def Let_def)

lemma sync_v061_preserves_legacy_admission_on_the_configured_set:
  assumes "decode_wire_packet raw = Some packet" "sync_operation (packet_core packet) \<in> accepted"
  shows "sync_v6_gate Sync_V061 accepted verify authenticate body_allowed authority raw =
    code_library_gate verify authenticate body_allowed authority raw"
  using assms sync_preserves_every_decoded_legacy_packet[OF assms(1)]
  by (cases "negotiated_version (boundary_profile authority) = 6";
      cases "code_check_declared_version raw (boundary_max_frame authority)";
      cases "length raw > boundary_max_frame authority")
     (simp_all add: sync_v6_gate_def sync_packet_for.simps code_library_gate_def
       code_decoded_gate_def sync_admit_decoded_def Let_def)

lemma sync_new_frame_old_and_unconfigured_refusals:
  assumes current: "negotiated_version (boundary_profile authority) = 6"
    and selected: "code_check_declared_version raw (boundary_max_frame authority) = None"
    and frame: "length raw \<le> boundary_max_frame authority"
    and decoded: "sync_decode_packet raw = Some packet"
    and added: "sync_added_operation (packet_core packet)"
    and excluded: "sync_operation (packet_core packet) \<notin> accepted"
  shows "sync_v6_gate Sync_V060 accepted verify authenticate body_allowed authority raw =
      Gate_Refused Invalid_Wire_Format"
    "sync_v6_gate Sync_V061 accepted verify authenticate body_allowed authority raw =
      Gate_Refused Unsupported_Wire_Version"
  using current selected frame decoded excluded sync_old_decoder_refuses_a_new_recognized_packet[OF decoded added]
  by (simp_all add: sync_v6_gate_def sync_admit_decoded_def Let_def)

fun sync_route_gate where
  "sync_route_gate consume (Gate_Refused reason) state = (state,Inl reason)"
| "sync_route_gate consume (Gate_Admitted packet) state =
    (case consume (packet_core packet) state of (next,result) \<Rightarrow> (next,Inr result))"

lemma sync_refusal_cannot_change_calls_or_effects:
  assumes "gate = Gate_Refused reason"
  shows "sync_route_gate consume gate state = (state,Inl reason)"
  using assms by simp

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_decoded_core_has_the_exact_bytes sync_decoded_packet_has_the_exact_bytes
    sync_old_decoder_refuses_a_new_recognized_packet sync_v061_preserves_legacy_admission_on_the_configured_set
    sync_new_frame_old_and_unconfigured_refusals sync_refusal_cannot_change_calls_or_effects})
  then () else error "Unexpected oracle in SyncCommitment wire preservation"
\<close>

end
