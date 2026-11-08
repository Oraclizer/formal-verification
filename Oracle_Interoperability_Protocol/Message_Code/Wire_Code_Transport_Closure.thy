theory Wire_Code_Transport_Closure
  imports Wire_Code_Oracle_Contract
begin

theorem every_transport_acceptance_has_the_exact_received_canonical_core:
  assumes result: "code_transport_oracle operand_check bytes authority max_nesting signature_valid attestation_valid prior =
      (verdict,after)"
    and accepted: "verdict = Code_Transport_First \<or> verdict = Code_Transport_Identical"
  obtains packet where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes" "wire_packet_wellformed packet"
    "signature_valid" "attestation_valid"
    "code_admit_packet (\<lambda>_ _ _. signature_valid) packet authority = None"
    "operand_check (packet_core packet) max_nesting = Code_Operand_Accept"
    "after = Some (encode_wire_core (packet_core packet))"
proof -
  obtain packet where packet: "decode_wire_packet bytes = Some packet"
    and signature: "code_admit_packet (\<lambda>_ _ _. signature_valid) packet authority = None"
    and attestation: "attestation_valid"
    and operand: "operand_check (packet_core packet) max_nesting = Code_Operand_Accept"
    and binding: "after = Some (encode_wire_core (packet_core packet))"
    using result accepted
    by (auto simp: code_transport_oracle_def code_transport_after_operands_def code_transport_refusal_def
      code_compare_binding_def Let_def
      split: option.splits code_operand_verdict.splits code_arrival.splits if_splits)
  have original: "encode_wire_packet packet = bytes" "wire_packet_wellformed packet"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF packet] by auto
  have verified: "signature_valid"
    using signature by (auto simp: code_admit_packet_def Let_def split: option.splits if_splits)
  show thesis by (rule that[OF packet original verified attestation signature operand binding])
qed

theorem an_accepted_transport_model_reuses_the_original_wire_gate_contract:
  assumes result: "code_transport_oracle operand_check bytes authority max_nesting signature_valid attestation_valid prior =
      (verdict,after)"
    and accepted: "verdict = Code_Transport_First \<or> verdict = Code_Transport_Identical"
    and threshold: "\<not> boundary_threshold_supported authority"
  obtains packet where
    "wire_gate (\<lambda>_ _ _. signature_valid) (\<lambda>_. attestation_valid)
      (\<lambda>profile core. operand_check core max_nesting = Code_Operand_Accept) authority bytes = Gate_Admitted packet"
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "current_wire_scope authority (packet_core packet)"
    "after = Some (encode_wire_core (packet_core packet))"
proof -
  obtain packet where packet: "decode_wire_packet bytes = Some packet"
    and original: "encode_wire_packet packet = bytes"
    and wellformed: "wire_packet_wellformed packet"
    and verified: "signature_valid" and attestation: "attestation_valid"
    and signature: "code_admit_packet (\<lambda>_ _ _. signature_valid) packet authority = None"
    and operand: "operand_check (packet_core packet) max_nesting = Code_Operand_Accept"
    and binding: "after = Some (encode_wire_core (packet_core packet))"
    by (rule every_transport_acceptance_has_the_exact_received_canonical_core[OF result accepted])
  have size: "length bytes \<le> boundary_max_frame authority"
    using result accepted
    by (auto simp: code_transport_oracle_def code_check_declared_version_def code_transport_refusal_def
      split: option.splits if_splits)
  have decoded: "code_decoded_gate (\<lambda>_ _ _. signature_valid) (\<lambda>_. attestation_valid)
      (\<lambda>profile core. operand_check core max_nesting = Code_Operand_Accept) authority bytes = Gate_Admitted packet"
    using size packet signature attestation operand by (simp add: code_decoded_gate_def)
  have gate: "wire_gate (\<lambda>_ _ _. signature_valid) (\<lambda>_. attestation_valid)
      (\<lambda>profile core. operand_check core max_nesting = Code_Operand_Accept) authority bytes = Gate_Admitted packet"
    using the_source_admission_order_matches_the_model_with_threshold_disabled[OF threshold] decoded by simp
  have scope: "current_wire_scope authority (packet_core packet)"
    using a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature[OF gate] by blast
  show thesis by (rule that[OF gate packet original scope binding])
qed

end
