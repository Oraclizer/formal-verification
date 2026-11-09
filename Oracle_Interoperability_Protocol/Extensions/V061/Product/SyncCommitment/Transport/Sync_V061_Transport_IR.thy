theory Sync_V061_Transport_IR
  imports "OIP_Sync_V061_Position_Direct_IR.Sync_V061_Direct_IR"
begin

definition sync_v061_operand_ir where
  "sync_v061_operand_ir depth core =
    (if sync_added_operation core then sync_direct_operand_ir depth core else code_typed_operand_ir depth core)"

definition sync_v061_operand_verdict where
  "sync_v061_operand_verdict core depth =
    (if sync_added_operation core then
       if sync_direct_operand_ir depth core = None then Code_Operand_Refuse Invalid_Wire_Format
       else Code_Operand_Accept
     else code_transport_operand_verdict core depth)"

definition sync_transport_oracle where
  "sync_transport_oracle operand_check raw authority depth signature_valid attestation_valid prior =
    (if negotiated_version (boundary_profile authority) \<noteq> 6
     then code_transport_refusal prior Unsupported_Wire_Version
     else case code_check_declared_version raw (boundary_max_frame authority) of
       Some reason \<Rightarrow> code_transport_refusal prior reason
     | None \<Rightarrow> (case sync_decode_packet raw of
         None \<Rightarrow> code_transport_refusal prior Invalid_Wire_Format
       | Some packet \<Rightarrow>
         (case code_admit_packet (\<lambda>_ _ _. signature_valid) packet authority of
            Some reason \<Rightarrow> code_transport_refusal prior reason
          | None \<Rightarrow> if \<not> attestation_valid then code_transport_refusal prior Invalid_Wire_Source
            else code_transport_after_operands operand_check packet depth prior)))"

lemma sync_transport_keeps_legacy_transport_when_its_operand_check_agrees:
  assumes "decode_wire_packet raw = Some packet"
    "operand_check (packet_core packet) depth = code_transport_operand_verdict (packet_core packet) depth"
  shows "sync_transport_oracle operand_check raw authority depth signature_valid attestation_valid prior =
    code_partial_transport_oracle raw authority depth signature_valid attestation_valid prior"
  using assms sync_preserves_every_decoded_legacy_packet[OF assms(1)]
  by (simp add: sync_transport_oracle_def code_partial_transport_oracle_def code_transport_oracle_def
    code_transport_after_operands_def split: option.splits)

lemma sync_transport_refusal_keeps_the_prior:
  assumes "sync_transport_oracle operand_check raw authority depth signature_valid attestation_valid prior =
    (Code_Transport_Refusal number, retained)"
  shows "retained = prior"
  using assms by (auto simp: sync_transport_oracle_def code_transport_after_operands_def
    code_transport_refusal_def Let_def split: option.splits code_operand_verdict.splits code_arrival.splits if_splits)

definition sync_typed_value_observation where
  "sync_typed_value_observation typed_check raw depth =
    Option.bind (sync_decode_packet raw) (\<lambda>packet.
      let core = packet_core packet in
      map_option (\<lambda>typed. (typed,encode_wire_core core,envelope_signing_bytes core,code_ir_transport_key core))
        (typed_check depth core))"

lemma sync_observation_is_from_the_admitted_packet_and_no_other:
  assumes "sync_typed_value_observation typed_check raw depth = Some (typed,exact,preimage,key)"
  obtains packet where "sync_decode_packet raw = Some packet"
    "typed_check depth (packet_core packet) = Some typed"
    "exact = encode_wire_core (packet_core packet)"
    "preimage = envelope_signing_bytes (packet_core packet)"
    "key = code_ir_transport_key (packet_core packet)"
    "encode_wire_packet packet = raw"
  using assms sync_decoded_packet_has_the_exact_bytes
  by (auto simp: sync_typed_value_observation_def Let_def bind_eq_Some_conv map_option_eq_Some)

definition sync_transport_flat_values where
  "sync_transport_flat_values operand_check typed_check bytes values version families atomicities schemes
        critical signature_valid attestation_valid prior_present prior =
    (if \<not> code_integer_octet_values bytes \<or> length values \<noteq> 13 \<or>
        \<not> code_integer_u64_values (values @ [version] @ families @ atomicities @ schemes) \<or>
        \<not> code_integer_common_host_values values \<or> (prior_present \<and> \<not> code_integer_octet_values prior)
     then (-1,False,[],False,[],[],[],[])
     else let raw = map nat_of_integer bytes; fields = map nat_of_integer values; depth = fields ! 12;
              scope = code_contract_boundary fields (nat_of_integer version) (map nat_of_integer families)
                      (map nat_of_integer atomicities) (map nat_of_integer schemes) critical;
              saved = (if prior_present then Some (map nat_of_integer prior) else None);
              (number,binding) = code_integer_reply
                (sync_transport_oracle operand_check raw scope depth signature_valid attestation_valid saved);
              present = (binding \<noteq> None);
              exact = (case binding of None \<Rightarrow> [] | Some bound \<Rightarrow> bound)
          in if number \<noteq> 0 \<and> number \<noteq> 1 then (number,present,exact,False,[],[],[],[])
             else case sync_typed_value_observation typed_check raw depth of
               None \<Rightarrow> (number,present,exact,False,[],[],[],[])
             | Some (typed,canonical,preimage,key) \<Rightarrow>
               (number,present,exact,True,map integer_of_nat typed,map integer_of_nat canonical,
                 map integer_of_nat preimage,map integer_of_nat key))"

definition sync_v061_transport_flat where
  "sync_v061_transport_flat = sync_transport_flat_values sync_v061_operand_verdict sync_v061_operand_ir"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_transport_keeps_legacy_transport_when_its_operand_check_agrees
      sync_transport_refusal_keeps_the_prior sync_observation_is_from_the_admitted_packet_and_no_other})
  then () else error "Unexpected oracle in the v0.6.1 typed transport comparison"
\<close>

export_code sync_v061_transport_flat
  in SML module_name OIP_Wire_Oracle_V061 file_prefix "oip_wire_values_v061_direct"

end
