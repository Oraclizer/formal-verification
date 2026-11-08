theory Wire_Code_Typed_Summary_ABI
  imports Wire_Code_Typed_Decode
begin

definition code_ir_transport_key :: "wire_core \<Rightarrow> nat list" where
  "code_ir_transport_key oip_binder_core =
    (case code_transport_key oip_binder_core of (oip_binder_deployment,oip_binder_source,oip_binder_principal,oip_binder_uuid) \<Rightarrow>
      code_ir_node 200 [code_ir_scalar oip_binder_deployment,code_ir_scalar oip_binder_source,
        code_ir_scalar oip_binder_principal,code_ir_bytes oip_binder_uuid])"

definition code_typed_observations ::
  "wire_bytes \<Rightarrow> nat list \<Rightarrow> (nat list \<times> wire_bytes \<times> wire_bytes \<times> nat list) option" where
  "code_typed_observations oip_binder_bytes oip_binder_values =
    (if length oip_binder_values \<noteq> 13 then None else
     Option.bind (decode_wire_packet oip_binder_bytes) (\<lambda>packet.
       map_option (\<lambda>oip_binder_typed. (oip_binder_typed,encode_wire_core (packet_core packet),
         envelope_signing_bytes (packet_core packet),code_ir_transport_key (packet_core packet)))
         (code_typed_operand_ir (oip_binder_values ! 12) (packet_core packet))))"

definition code_typed_transport_flat_oracle ::
  "integer list \<Rightarrow> integer list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow>
    (integer \<times> bool \<times> integer list \<times> bool \<times> integer list \<times> integer list \<times> integer list \<times> integer list)" where
  "code_typed_transport_flat_oracle oip_binder_bytes oip_binder_values version oip_binder_families oip_binder_atomicities oip_binder_schemes oip_binder_critical
      oip_binder_signature_valid oip_binder_attestation_valid oip_binder_prior_present oip_binder_prior =
    (let (oip_binder_status,oip_binder_present,oip_binder_binding) = code_partial_transport_flat_oracle oip_binder_bytes oip_binder_values version oip_binder_families oip_binder_atomicities oip_binder_schemes
        oip_binder_critical oip_binder_signature_valid oip_binder_attestation_valid oip_binder_prior_present oip_binder_prior
     in if oip_binder_status = 0 \<or> oip_binder_status = 1 then
       (case code_typed_observations (map nat_of_integer oip_binder_bytes) (map nat_of_integer oip_binder_values) of
          None \<Rightarrow> (oip_binder_status,oip_binder_present,oip_binder_binding,False,[],[],[],[])
        | Some (oip_binder_typed,oip_binder_core,oip_binder_preimage,oip_binder_key) \<Rightarrow> (oip_binder_status,oip_binder_present,oip_binder_binding,True,
            map integer_of_nat oip_binder_typed,map integer_of_nat oip_binder_core,map integer_of_nat oip_binder_preimage,map integer_of_nat oip_binder_key))
     else (oip_binder_status,oip_binder_present,oip_binder_binding,False,[],[],[],[]))"

definition code_typed_transport_prefix where
  "code_typed_transport_prefix oip_binder_reply =
    (case oip_binder_reply of (oip_binder_status,oip_binder_present,oip_binder_binding,oip_binder_observed,oip_binder_typed,oip_binder_core,oip_binder_preimage,oip_binder_key) \<Rightarrow> (oip_binder_status,oip_binder_present,oip_binder_binding))"

lemma the_typed_summary_does_not_replace_the_existing_transport_decision:
  "code_typed_transport_prefix
      (code_typed_transport_flat_oracle oip_binder_bytes oip_binder_values version oip_binder_families oip_binder_atomicities oip_binder_schemes oip_binder_critical
        oip_binder_signature_valid oip_binder_attestation_valid oip_binder_prior_present oip_binder_prior) =
    code_partial_transport_flat_oracle oip_binder_bytes oip_binder_values version oip_binder_families oip_binder_atomicities oip_binder_schemes oip_binder_critical
      oip_binder_signature_valid oip_binder_attestation_valid oip_binder_prior_present oip_binder_prior"
  by (simp add: code_typed_transport_flat_oracle_def code_typed_transport_prefix_def Let_def
    split: prod.splits option.splits if_splits)

lemma a_transport_refusal_does_not_supply_fake_typed_observations:
  assumes old: "code_partial_transport_flat_oracle oip_binder_bytes oip_binder_values version oip_binder_families oip_binder_atomicities oip_binder_schemes oip_binder_critical
      oip_binder_signature_valid oip_binder_attestation_valid oip_binder_prior_present oip_binder_prior = (oip_binder_status,oip_binder_present,oip_binder_binding)"
    and refused: "oip_binder_status \<noteq> 0" "oip_binder_status \<noteq> 1"
  shows "code_typed_transport_flat_oracle oip_binder_bytes oip_binder_values version oip_binder_families oip_binder_atomicities oip_binder_schemes oip_binder_critical
      oip_binder_signature_valid oip_binder_attestation_valid oip_binder_prior_present oip_binder_prior = (oip_binder_status,oip_binder_present,oip_binder_binding,False,[],[],[],[])"
  using old refused by (simp add: code_typed_transport_flat_oracle_def Let_def)

lemma a_typed_observation_uses_only_its_own_decoded_packet_and_typed_result:
  assumes "code_typed_observations oip_binder_bytes oip_binder_values = Some (oip_binder_typed,oip_binder_core,oip_binder_preimage,oip_binder_key)"
  obtains packet where "length oip_binder_values = 13" "decode_wire_packet oip_binder_bytes = Some packet"
    "code_typed_operand_ir (oip_binder_values ! 12) (packet_core packet) = Some oip_binder_typed"
    "oip_binder_core = encode_wire_core (packet_core packet)"
    "oip_binder_preimage = envelope_signing_bytes (packet_core packet)"
    "oip_binder_key = code_ir_transport_key (packet_core packet)"
  using assms by (auto simp: code_typed_observations_def bind_eq_Some_conv
    split: if_splits option.splits)

lemma the_summary_transport_key_has_the_authenticated_components:
  "code_ir_transport_key oip_binder_core = code_ir_node 200
    [code_ir_scalar (wire_deployment oip_binder_core),code_ir_scalar (wire_source_domain oip_binder_core),
     code_ir_scalar (wire_principal oip_binder_core),code_ir_bytes (wire_uuid oip_binder_core)]"
  by (simp add: code_ir_transport_key_def code_transport_key_def)

lemma a_summary_packet_reencoding_is_the_received_canonical_packet:
  assumes "decode_wire_packet oip_binder_bytes = Some packet"
  shows "encode_wire_packet packet = oip_binder_bytes"
  using every_accepted_wire_message_has_exactly_the_received_bytes[OF assms] by blast

definition code_typed_summary_identity :: "unit \<Rightarrow> integer list list" where
  "code_typed_summary_identity oip_binder_ignored = map (map integer_of_nat \<circ> code_json_ascii)
    [''OIP_TYPED_OPERAND_INTEGER_IR_V1'',''intinf-typed-flat-v2'',
     ''OIP_Wire_Oracle.code_typed_transport_flat_oracle'',
     ''status,binding-present,binding,summary-present,typed-ir,canonical-core,signing-preimage,transport-key'']"

lemma the_typed_summary_identity_has_four_independent_interface_fields:
  "length (code_typed_summary_identity ()) = 4"
  by (simp add: code_typed_summary_identity_def)

text \<open>
  Input order and the first three returned values are unchanged. The new
  fields do not participate in acceptance, refusal, binding or primitive
  booleans. A strict consumer MUST fail an accepted row with observed=False.
  Refusals have no observation and JSON null for each of the four fields.
  Integers are serialized as canonical decimal strings; adapters do not
  reconstruct typed values from the received raw operand words.
  The original six-field code_model_identity records the model's source
  fingerprint independently of this observation interface.
  This interface identity is not a caller-supplied fingerprint echo.
\<close>

end
