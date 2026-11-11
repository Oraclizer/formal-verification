theory Retained_Transition_Integrity_Model_Link
  imports "OIP_Message_Code.Wire_Code_Typed_Summary_Check"
    "OIP_Reference_Execution.Reference_Read_Code"
begin

record rti_image =
  rti_epoch :: nat
  rti_revision :: nat
  rti_policy :: "wire_bytes option"
  rti_assets :: "nat list"
  rti_owners :: "nat list"
  rti_contexts :: "nat list list"
  rti_transport :: "(nat list \<times> wire_bytes) list"
  rti_prefixes :: "wire_bytes list"
  rti_prefix_assets :: "nat list list"
  rti_capture :: wire_bytes

definition rti_octets where
  "rti_octets rti_bytes \<longleftrightarrow> list_all (\<lambda>rti_byte. rti_byte < 256) rti_bytes"

definition rti_decode_image :: "nat list list list \<Rightarrow> rti_image option" where
  "rti_decode_image rti_input =
    (case rti_input of
       [[[rti_e,rti_r],rti_binding,rti_asset_keys,rti_owner_keys,rti_view],
        rti_endpoints,rti_bindings,rti_history,rti_history_keys] \<Rightarrow>
          (let rti_pairs = map (\<lambda>rti_row. (take 19 rti_row,drop 19 rti_row)) rti_bindings in
           if (rti_binding = [] \<or> length rti_binding = 32) \<and> rti_octets rti_binding \<and>
              sorted_wrt (<) rti_asset_keys \<and> sorted_wrt (<) rti_owner_keys \<and>
              list_all (\<lambda>rti_row. length rti_row = 3) rti_endpoints \<and>
              sorted_wrt (<) (map hd rti_endpoints) \<and> distinct (map fst rti_pairs) \<and>
              list_all (\<lambda>rti_row. 19 < length rti_row \<and> rti_octets (drop 3 rti_row)) rti_bindings \<and>
              length rti_history = length rti_history_keys \<and>
              list_all rti_octets rti_history \<and> list_all (sorted_wrt (<)) rti_history_keys \<and>
              rti_octets rti_view
           then Some \<lparr>rti_epoch = rti_e,rti_revision = rti_r,
               rti_policy = (if rti_binding = [] then None else Some rti_binding),
               rti_assets = rti_asset_keys,rti_owners = rti_owner_keys,rti_contexts = rti_endpoints,
               rti_transport = rti_pairs,rti_prefixes = rti_history,rti_prefix_assets = rti_history_keys,
               rti_capture = rti_view\<rparr>
           else None)
     | _ \<Rightarrow> None)"

definition rti_same_epoch_policy where
  "rti_same_epoch_policy rti_previous rti_candidate \<longleftrightarrow>
    rti_epoch rti_previous \<noteq> rti_epoch rti_candidate \<or>
    rti_policy rti_previous = rti_policy rti_candidate"

definition rti_preserves_transport where
  "rti_preserves_transport rti_old rti_next \<longleftrightarrow>
    list_all (\<lambda>rti_row. code_compare_binding (map_of rti_next (fst rti_row)) (snd rti_row) = Code_Identical) rti_old"

definition rti_preceding_history where
  "rti_preceding_history rti_old rti_next \<longleftrightarrow> take (length rti_old) rti_next = rti_old"

definition rti_endpoint_registry where
  "rti_endpoint_registry rti_image_value \<longleftrightarrow>
    rti_contexts rti_image_value \<noteq> [] \<and>
    list_all (\<lambda>rti_row. rti_row ! 0 = rti_row ! 1 \<and> rti_row ! 2 = rti_epoch rti_image_value)
      (rti_contexts rti_image_value)"

definition rti_current_view where
  "rti_current_view rti_image_value \<longleftrightarrow>
    (let rti_e = rti_epoch rti_image_value; rti_history = rti_prefixes rti_image_value;
         rti_model_history = \<lparr>reference_history_epoch = rti_e,reference_history_prefixes = rti_history\<rparr>
     in native_read_history_related rti_e (rti_revision rti_image_value) rti_history rti_model_history \<and>
        last rti_history = rti_capture rti_image_value)"

definition rti_checks :: "rti_image \<Rightarrow> rti_image \<Rightarrow> bool \<Rightarrow> nat list" where
  "rti_checks rti_previous rti_candidate rti_other_guards =
    (let rti_owner_ok = rti_owners rti_candidate = rti_assets rti_candidate;
         rti_policy_ok = rti_same_epoch_policy rti_previous rti_candidate;
         rti_transport_ok = rti_preserves_transport (rti_transport rti_previous) (rti_transport rti_candidate);
         rti_history_ok = rti_preceding_history (rti_prefixes rti_previous) (rti_prefixes rti_candidate);
         rti_endpoint_ok = rti_endpoint_registry rti_candidate;
         rti_history_keys_ok = list_all (\<lambda>rti_keys. rti_keys = rti_assets rti_candidate) (rti_prefix_assets rti_candidate);
         rti_current_ok = rti_current_view rti_candidate;
         rti_prev_endpoint_ok = rti_endpoint_registry rti_previous;
         rti_endpoint_keys_ok = map hd (rti_contexts rti_previous) = map hd (rti_contexts rti_candidate);
         rti_prev_current_ok = rti_current_view rti_previous;
         rti_bits = [rti_owner_ok,rti_policy_ok,rti_transport_ok,rti_history_ok,
           rti_endpoint_ok,rti_history_keys_ok,rti_current_ok,
           rti_prev_endpoint_ok,rti_endpoint_keys_ok,rti_prev_current_ok];
         rti_decision = (if \<not> rti_endpoint_ok \<or> \<not> rti_owner_ok then 0
           else if \<not> rti_other_guards then 2 else if list_all id rti_bits then 1 else 0)
     in map (\<lambda>rti_fact. if rti_fact then 1 else 0) (rti_bits @ [rti_other_guards]) @ [rti_decision])"

lemma rti_transport_check_is_exact_retained_lookup:
  "code_compare_binding rti_prior rti_exact = Code_Identical \<longleftrightarrow> rti_prior = Some rti_exact"
  by (cases rti_prior) (simp_all add: code_compare_binding_def)

lemma rti_reference_advance_preserves_preceding_history:
  "rti_preceding_history (reference_history_prefixes rti_history)
    (reference_history_prefixes (record_reference_advance rti_e rti_steps rti_snapshot rti_history))"
  by (cases rti_steps) (simp_all add: rti_preceding_history_def record_reference_advance_def)

definition rti_u64 :: "integer \<Rightarrow> bool" where
  "rti_u64 rti_word \<longleftrightarrow> 0 \<le> rti_word \<and> rti_word < 18446744073709551616"

definition rti_integer_abi ::
  "integer list list list \<Rightarrow> integer list list list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "rti_integer_abi rti_old rti_next rti_other =
    (if list_all (list_all (list_all rti_u64)) (rti_old @ rti_next) \<and>
        (rti_other = [0] \<or> rti_other = [1]) then
       (case (rti_decode_image (map (map (map nat_of_integer)) rti_old),
              rti_decode_image (map (map (map nat_of_integer)) rti_next)) of
          (Some rti_before,Some rti_after) \<Rightarrow>
            Some (map integer_of_nat (rti_checks rti_before rti_after (rti_other = [1])))
        | _ \<Rightarrow> None)
     else None)"

thm_oracles rti_transport_check_is_exact_retained_lookup rti_reference_advance_preserves_preceding_history
  the_native_cut_and_its_selected_prefixes_give_the_same_model_values

export_code rti_integer_abi in SML
  module_name OIP_Retained_Transition_Typed_ABI file_prefix "oip_retained_transition_integrity_abi"

end
