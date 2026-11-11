theory Exact_Receipt_Core_Comparison
  imports "OIP_Message_Code.Wire_Code_Oracle_Codegen"
    "OIP_Message_Code.Wire_Code_Typed_Summary_ABI"
begin

text \<open>The supplied stored Core describes one candidate binding. Both
lookup keys come from the canonical decoders. This comparison does not
supply a selected journal, a receipt, or a financial effect.\<close>

definition exact_receipt_core_comparison ::
  "wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> (nat list \<times> nat list \<times> nat) option" where
  "exact_receipt_core_comparison stored nested =
    Option.bind (decode_wire_core stored) (\<lambda>stored_core.
      map_option (\<lambda>nested_core.
        let retained = map_of [(code_transport_key stored_core,stored)] (code_transport_key nested_core);
            exact = encode_wire_core nested_core;
            result = (case code_compare_binding retained exact of
              Code_First \<Rightarrow> 0 | Code_Identical \<Rightarrow> 1 | Code_Replay_Conflict \<Rightarrow> 2)
        in (code_ir_transport_key stored_core,code_ir_transport_key nested_core,result))
      (decode_wire_core nested))"

lemma the_supplied_receipt_slot_compares_the_decoded_key_and_exact_original_bytes:
  assumes stored: "decode_wire_core saved = Some stored_core"
    and requested: "decode_wire_core nested = Some nested_core"
  shows "exact_receipt_core_comparison saved nested =
    Some (code_ir_transport_key stored_core,code_ir_transport_key nested_core,
      if authenticated_wire_message_id stored_core \<noteq> authenticated_wire_message_id nested_core then 0
      else if saved = nested then 1 else 2)"
proof -
  have exact: "encode_wire_core nested_core = nested"
    by (rule conjunct2[OF accepted_core_bytes_preserve_all_original_fields[OF requested]])
  show ?thesis
    unfolding exact_receipt_core_comparison_def stored requested
      the_source_transport_key_has_the_exact_authenticated_model_components
    by (cases "authenticated_wire_message_id stored_core = authenticated_wire_message_id nested_core")
      (simp_all add: exact Let_def code_compare_binding_def split: if_splits)
qed

definition exact_receipt_core_integer_comparison ::
  "integer list \<Rightarrow> integer list \<Rightarrow> (integer list \<times> integer list \<times> integer) option" where
  "exact_receipt_core_integer_comparison stored nested =
    (if code_integer_octet_values stored \<and> code_integer_octet_values nested then
       map_option (\<lambda>(old_key,new_key,comparison).
         (map integer_of_nat old_key,map integer_of_nat new_key,integer_of_nat comparison))
       (exact_receipt_core_comparison (map nat_of_integer stored) (map nat_of_integer nested))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      the_supplied_receipt_slot_compares_the_decoded_key_and_exact_original_bytes
      the_source_transport_key_has_the_exact_authenticated_model_components
      a_conflicting_retained_core_is_never_overwritten})
  then () else error "Unexpected oracle in exact receipt Core comparison"
\<close>

export_code exact_receipt_core_integer_comparison
  in SML module_name OIP_Exact_Receipt_Core_ABI file_prefix "oip_exact_receipt_core_abi"

end
