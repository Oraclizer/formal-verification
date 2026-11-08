theory Wire_Code_Response_Boundary_Result
  imports Wire_Code_Response_Boundary_Input
begin

definition code_rbound_observation ::
  "nat \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> response_fixed_observation option" where
  "code_rbound_observation oip_binder_mode oip_binder_values oip_binder_retained_present oip_binder_retained =
    (if oip_binder_mode = 0 then Option.bind (code_rbound_action oip_binder_values) (\<lambda>(oip_binder_root,oip_binder_reply).
       if \<not> oip_binder_retained_present then
         (if oip_binder_retained = [] then Some (Response_Fixed_Received oip_binder_reply None) else None)
       else Option.bind (code_rbound_receipt oip_binder_retained) (\<lambda>(oip_binder_stored_root,oip_binder_receipt).
         let oip_binder_full_root_matches = (case oip_binder_reply of
               Code_Source_Spend_Action (Code_Source_Spend_Executed oip_binder_position) \<Rightarrow> oip_binder_root = oip_binder_stored_root
             | _ \<Rightarrow> True)
         in Some (Response_Fixed_Received oip_binder_reply (if oip_binder_full_root_matches then Some oip_binder_receipt else None))))
     else if oip_binder_retained_present \<or> oip_binder_retained \<noteq> [] then None
     else if oip_binder_mode = 1 then map_option Response_Fixed_Resolved (code_rbound_resolution oip_binder_values)
     else if oip_binder_mode = 2 then map_option Response_Fixed_Error (code_rbound_error oip_binder_values)
     else None)"

definition code_response_result_flat_oracle ::
  "integer \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow>
    (bool \<times> integer \<times> bool \<times> integer)" where
  "code_response_result_flat_oracle oip_binder_mode oip_binder_values oip_binder_retained_present oip_binder_retained =
    (if \<not> code_integer_u64_values (oip_binder_mode # oip_binder_values @ oip_binder_retained) then (False,-1,False,0)
     else case code_rbound_observation (nat_of_integer oip_binder_mode) (map nat_of_integer oip_binder_values)
         oip_binder_retained_present (map nat_of_integer oip_binder_retained) of None \<Rightarrow> (False,-1,False,0)
      | Some oip_binder_observation \<Rightarrow>
          let (oip_binder_number,oip_binder_position) = response_fixed_result oip_binder_observation in
          (True,integer_of_nat oip_binder_number,oip_binder_position \<noteq> None,integer_of_nat ((case oip_binder_position of None \<Rightarrow> 0 | Some oip_option_value \<Rightarrow> oip_option_value))))"

lemma a_parsed_received_value_is_consumed_by_the_existing_result_converter:
  assumes oip_binder_domain: "code_integer_u64_values (oip_binder_mode # oip_binder_values @ oip_binder_retained)"
    and oip_binder_parsed: "code_rbound_observation (nat_of_integer oip_binder_mode) (map nat_of_integer oip_binder_values)
      oip_binder_retained_present (map nat_of_integer oip_binder_retained) = Some oip_binder_observation"
  shows "code_response_result_flat_oracle oip_binder_mode oip_binder_values oip_binder_retained_present oip_binder_retained =
    (True,integer_of_nat (fst (response_fixed_result oip_binder_observation)),
      snd (response_fixed_result oip_binder_observation) \<noteq> None,
      integer_of_nat ((case snd (response_fixed_result oip_binder_observation) of None \<Rightarrow> 0 | Some oip_option_value \<Rightarrow> oip_option_value)))"
  using oip_binder_domain oip_binder_parsed by (simp add: code_response_result_flat_oracle_def split: prod.splits)

lemma different_actual_spend_roots_cannot_supply_a_matching_projected_receipt:
  assumes roots: "(oip_binder_first_domain,oip_binder_first_event) \<noteq> (oip_binder_second_domain,oip_binder_second_event)"
  shows "code_rbound_observation 0 [2,0,oip_binder_first_domain,oip_binder_first_event,oip_binder_position] True
      [2,0,oip_binder_second_domain,oip_binder_second_event,oip_binder_position] =
    Some (Response_Fixed_Received
      (Code_Source_Spend_Action (Code_Source_Spend_Executed oip_binder_position)) None)"
  using roots by (simp add: code_rbound_observation_def code_rbound_action_def
    code_rbound_receipt_def code_rbound_spend_def Let_def)

lemma a_root_mismatch_keeps_the_existing_unresolved_conversion:
  assumes roots: "(oip_binder_first_domain,oip_binder_first_event) \<noteq> (oip_binder_second_domain,oip_binder_second_event)"
  shows "map_option response_fixed_result
      (code_rbound_observation 0 [2,0,oip_binder_first_domain,oip_binder_first_event,oip_binder_position] True
        [2,0,oip_binder_second_domain,oip_binder_second_event,oip_binder_position]) = Some (50,None)"
  using different_actual_spend_roots_cannot_supply_a_matching_projected_receipt[OF roots] by simp

lemma matching_full_spend_values_keep_the_actual_commit:
  "map_option response_fixed_result
      (code_rbound_observation 0 [2,0,oip_binder_domain,oip_binder_event,oip_binder_position] True
        [2,0,oip_binder_domain,oip_binder_event,oip_binder_position]) = Some (28,Some oip_binder_position)"
  by (simp add: code_rbound_observation_def code_rbound_action_def
    code_rbound_receipt_def code_rbound_spend_def Let_def)

lemma retained_legal_busy_precedes_the_delivery_busy_fallback:
  "map_option response_fixed_result
      (code_rbound_observation 0 [1,2,9] True [1,2,9]) = Some (2,None)"
  "map_option response_fixed_result
      (code_rbound_observation 0 [1,2,9] False []) = Some (55,None)"
  by (simp_all add: code_rbound_observation_def code_rbound_action_def
    code_rbound_receipt_def code_rbound_legal_def Let_def)

lemma the_same_boundary_outcome_supplies_the_exact_recorded_position:
  "map_option response_fixed_result
      (code_rbound_observation 0 [0,0,0,0,4,1,oip_binder_position] True
        [0,0,0,4,1,oip_binder_position]) = Some (12,Some oip_binder_position)"
  by (simp add: code_rbound_observation_def code_rbound_action_def code_rbound_collection_def
    code_rbound_outcome_def code_rbound_position_def code_rbound_accepted_reply_def
    code_rbound_receipt_def code_source_ordinary_result_def Let_def)

lemma a_boundary_error_tag_is_converted_instead_of_being_echoed:
  "map_option response_fixed_result (code_rbound_observation 2 [0] False []) = Some (70,None)"
  "map_option response_fixed_result (code_rbound_observation 2 [14] False []) = Some (56,None)"
  by (simp_all add: code_rbound_observation_def code_rbound_error_def code_source_error_result_def Let_def)

text \<open>
  The old source Spend reply projection contains only its commit. Actual
  Rust SpendReply::Executed also has root, and reply==stored compares root.
  This helper retains both source root tuples until that equality is decided.
  It never replaces a full equality with an input bool. Only then is the old
  projected receipt passed to the existing result converter; a mismatched
  executed root uses its existing no-matching-receipt fallback.
  These are typed-return boundary fixtures/observations. No product runner,
  whole source verdict, source after-state or observed response number is
  supplied as a model answer. Dispatcher producer provenance is separate.
\<close>

end
