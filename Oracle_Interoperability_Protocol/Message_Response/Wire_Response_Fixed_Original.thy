theory Wire_Response_Fixed_Original
  imports Wire_Response_Fixed_Preimage
begin

record response_fixed_site =
  response_site_profile :: "nat \<times> nat \<times> nat"
  response_site_ordered_control :: "unit option"
  response_site_security_ordered_profile :: "(nat \<times> nat \<times> nat) option"

definition response_fixed_channel_guard where
  "response_fixed_channel_guard config channel =
    \<lparr>guard_channel_version = negotiated_version (response_channel_profile channel),
      guard_channel_deployment = response_channel_deployment channel,guard_channel_local = response_channel_local channel,
      guard_channel_remote = response_channel_remote channel,guard_channel_expires = response_channel_expires channel,
      guard_channel_peer_key = response_channel_remote_key channel,
      guard_channel_current = response_fixed_channel_current config channel\<rparr>"

definition response_fixed_original_signature where
  "response_fixed_original_signature curve_verify channel original =
    code_original_signature_refusal (response_channel_profile channel)
      (\<lambda>core bytes signature. curve_verify (response_channel_remote_key channel) bytes signature) original"

definition response_fixed_original_preflight where
  "response_fixed_original_preflight config channel site curve_verify frame_limit bytes =
    code_original_response_preflight (response_channel_profile channel)
      (response_fixed_channel_guard config channel)
      (response_site_ordered_control site \<noteq> None)
      (response_site_security_ordered_profile site = Some (response_site_profile site))
      (fst (response_site_profile site)) frame_limit (response_fixed_atomicity channel)
      (\<lambda>core preimage signature. curve_verify (response_channel_remote_key channel) preimage signature) bytes"

definition response_fixed_raw_core where
  "response_fixed_raw_core bytes =
    (case read_canonical_proto_fields bytes of
       Some [Proto_Bytes core_tag raw,Proto_Bytes signature_tag signature] \<Rightarrow>
         if core_tag = 1 \<and> signature_tag = 2 then Some raw else None
     | _ \<Rightarrow> None)"

lemma response_fixed_canonical_packet_getter_keeps_the_received_core_bytes:
  assumes "decode_wire_packet bytes = Some packet"
  shows "response_fixed_raw_core bytes = Some (encode_wire_core (packet_core packet))"
  using assms accepted_core_bytes_preserve_all_original_fields
  by (auto simp: response_fixed_raw_core_def decode_wire_packet_def Let_def
    split: option.splits list.splits proto_field.splits if_splits)

theorem response_fixed_original_signature_reads_only_the_original_and_channel_peer:
  assumes "response_fixed_original_signature curve_verify channel original = None"
  shows "curve_verify (response_channel_remote_key channel)
      (envelope_signing_bytes (packet_core original)) (packet_signature original)"
    "wire_signature_scheme (packet_core original) \<noteq> 2"
  using assms by (auto simp: response_fixed_original_signature_def code_original_signature_refusal_def Let_def split: if_splits)

theorem response_fixed_preflight_selects_one_canonical_original_and_exact_peer_preimage:
  assumes admitted: "response_fixed_original_preflight config channel site curve_verify frame_limit bytes = Inr (packet,call_id)"
  shows "decode_wire_packet bytes = Some packet"
    "response_fixed_raw_core bytes = Some (encode_wire_core (packet_core packet))"
    "curve_verify (response_channel_remote_key channel)
      (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
    "response_site_ordered_control site \<noteq> None"
    "response_site_security_ordered_profile site = Some (response_site_profile site)"
    "response_fixed_channel_current config channel"
proof -
  have actual_preflight: "code_original_response_preflight (response_channel_profile channel)
      (response_fixed_channel_guard config channel) (response_site_ordered_control site \<noteq> None)
      (response_site_security_ordered_profile site = Some (response_site_profile site))
      (fst (response_site_profile site)) frame_limit (response_fixed_atomicity channel)
      (\<lambda>core preimage signature. curve_verify (response_channel_remote_key channel) preimage signature) bytes = Inr (packet,call_id)"
    using admitted by (simp add: response_fixed_original_preflight_def)
  have selected: "decode_wire_packet bytes = Some packet"
    and verified: "curve_verify (response_channel_remote_key channel)
      (envelope_signing_bytes (packet_core packet)) (packet_signature packet)"
    using a_preflight_original_is_verified_with_the_peer_key_before_a_response[OF actual_preflight] by auto
  show "decode_wire_packet bytes = Some packet" by (rule selected)
  show "response_fixed_raw_core bytes = Some (encode_wire_core (packet_core packet))"
    by (rule response_fixed_canonical_packet_getter_keeps_the_received_core_bytes[OF selected])
  show "curve_verify (response_channel_remote_key channel)
      (envelope_signing_bytes (packet_core packet)) (packet_signature packet)" by (rule verified)
  show "response_site_ordered_control site \<noteq> None"
    "response_site_security_ordered_profile site = Some (response_site_profile site)"
    "response_fixed_channel_current config channel"
    using admitted by (auto simp: response_fixed_original_preflight_def code_original_response_preflight_def
      response_fixed_channel_guard_def split: if_splits)
qed

text \<open>
  The site fields are the exact value projections of RecoveryProfile
  (deployment,format,authority_profile), ordered_wire_control presence and
  ordered_revocation_profile. They are not a passed-whole-path flag. The
  channel-current predicate is rebuilt from the one immutable signer config.
  The original Core bytes are a getter from the received canonical packet,
  not an independently supplied original or an assumed preimage equality.
\<close>

end
