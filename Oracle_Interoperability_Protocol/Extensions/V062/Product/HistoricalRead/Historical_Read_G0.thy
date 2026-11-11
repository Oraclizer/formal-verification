theory Historical_Read_G0
  imports "OIP_Reference_Execution.Reference_Read_Code" "OIP_Message_Code.Wire_Code_Read_Service"
begin

text \<open>
  ApplicationValue only. Access and availability are checked upstream inputs.
  The four projections are the observation contract of the authorized fixture
  Reserve, Write, Cancel trace, not a substitute for proving those actions were
  accepted by the native endpoint. Each prefix keeps its own visibility.
\<close>

record historical_app_projection =
  historical_units :: nat
  historical_locked :: bool
  historical_unpublished_touch :: bool
  historical_registered :: bool

datatype historical_snapshot_reply =
    Historical_Visible application_value
  | Historical_Hidden
  | Historical_Missing

definition historical_project_value where
  "historical_project_value projection =
    (if historical_unpublished_touch projection \<or> historical_locked projection then Historical_Hidden
     else if historical_registered projection then Historical_Visible (Units_Value (historical_units projection))
     else Historical_Missing)"

fun historical_labelled_reply :: "(nat \<times> historical_snapshot_reply) option \<Rightarrow> product_read_reply" where
  "historical_labelled_reply None = Product_Read_Unavailable"
| "historical_labelled_reply (Some (named_index, Historical_Visible observed_value)) =
    Historical_Prefix_Value named_index observed_value"
| "historical_labelled_reply (Some (named_index, Historical_Hidden)) = Product_Read_Busy"
| "historical_labelled_reply (Some (named_index, Historical_Missing)) = Product_Read_Unavailable"

fun historical_current_reply :: "(product_cut \<times> historical_snapshot_reply) option \<Rightarrow> product_read_reply" where
  "historical_current_reply None = Product_Read_Busy"
| "historical_current_reply (Some (selected_cut, Historical_Visible observed_value)) = Current_Cut_Value selected_cut observed_value"
| "historical_current_reply (Some (selected_cut, Historical_Hidden)) = Product_Read_Busy"
| "historical_current_reply (Some (selected_cut, Historical_Missing)) = Product_Read_Unavailable"

definition historical_wrong_last_index where
  "historical_wrong_last_index permitted project requested_index prefixes =
    (if permitted \<and> requested_index < length prefixes
     then Some (requested_index, project (last prefixes)) else None)"

definition historical_native_read where
  "historical_native_read substitute_last access_checked available requested_index prefixes =
    (if \<not> access_checked then Product_Read_Rejected
     else if \<not> available then Product_Read_Unavailable
     else historical_labelled_reply
       (if substitute_last then historical_wrong_last_index True historical_project_value requested_index prefixes
        else native_history_read_value True historical_project_value requested_index prefixes))"

definition historical_native_current where
  "historical_native_current access_checked available expected_cut epoch revision prefixes =
    (if \<not> access_checked then Product_Read_Rejected
     else if \<not> available then Product_Read_Unavailable
     else historical_current_reply
       (native_current_read_value True historical_project_value expected_cut epoch revision prefixes))"

definition historical_fixture_projection where
  "historical_fixture_projection units_input locked_input =
    \<lparr>historical_units = units_input, historical_locked = locked_input,
     historical_unpublished_touch = False, historical_registered = True\<rparr>"

definition historical_fixture_prefixes where
  "historical_fixture_prefixes initial written =
    native_resize_read_prefixes 3 (historical_fixture_projection written False)
      (native_resize_read_prefixes 2 (historical_fixture_projection written True)
        (native_resize_read_prefixes 1 (historical_fixture_projection initial True)
          [historical_fixture_projection initial False]))"

definition historical_fixture_history where
  "historical_fixture_history epoch initial written =
    record_reference_advance epoch 1 (historical_fixture_projection written False)
      (record_reference_advance epoch 1 (historical_fixture_projection written True)
        (record_reference_advance epoch 1 (historical_fixture_projection initial True)
          (initialize_reference_history epoch (historical_fixture_projection initial False))))"

lemma historical_native_resize_and_reference_recording_agree:
  "native_read_history_related epoch 3 (historical_fixture_prefixes initial written)
    (historical_fixture_history epoch initial written)"
  by (simp add: native_read_history_related_def historical_fixture_prefixes_def historical_fixture_history_def
      native_resize_read_prefixes_def record_reference_advance_def initialize_reference_history_def)

lemma historical_read_reuses_exact_named_reference_prefix:
  assumes aligned: "native_read_history_related epoch revision prefixes history"
  shows "historical_native_read False True True requested_index prefixes =
    historical_labelled_reply (historical_reference_observation True historical_project_value requested_index history)"
proof -
  have same: "native_history_read_value True historical_project_value requested_index prefixes =
    historical_reference_observation True historical_project_value requested_index history"
    by (rule the_native_cut_and_its_selected_prefixes_give_the_same_model_values(2)[OF aligned])
  show ?thesis by (simp add: historical_native_read_def same)
qed

lemma historical_query2_reuses_the_existing_service_selector:
  assumes "wire_message_family core = Wire_Query"
    "wire_opcode (wire_operation_body core) = 2"
    "wire_words (wire_operation_body core) = [selected_session,requested_index,1,selected_asset]"
    "wire_blobs (wire_operation_body core) = []"
    "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core = Some
    (Service_Read token \<lparr>proof_session = selected_session,proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) (Historical_Data (Application_Value selected_asset) requested_index) None)"
  using assms by (simp add: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decode_wire_query_body_def parse_wire_application_query_def Let_def)

lemma historical_g0_old_unavailable_and_current:
  "historical_native_read False True True 0 (historical_fixture_prefixes 0 9) =
    Historical_Prefix_Value 0 (Units_Value 0)"
  "historical_native_read False True True 4 (historical_fixture_prefixes 0 9) = Product_Read_Unavailable"
  "historical_native_current True True \<lparr>cut_authority_epoch = 9,cut_revision = 3\<rparr> 9 3
      (historical_fixture_prefixes 0 9) =
    Current_Cut_Value \<lparr>cut_authority_epoch = 9,cut_revision = 3\<rparr> (Units_Value 9)"
  by (simp_all add: historical_native_read_def historical_native_current_def
      native_history_read_value_def native_current_read_value_def historical_fixture_prefixes_def
      native_resize_read_prefixes_def historical_project_value_def historical_fixture_projection_def)

lemma historical_g0_each_named_prefix_keeps_its_visibility:
  "historical_native_read False True True 1 (historical_fixture_prefixes 0 9) = Product_Read_Busy"
  "historical_native_read False True True 2 (historical_fixture_prefixes 0 9) = Product_Read_Busy"
  "historical_native_read False True True 3 (historical_fixture_prefixes 0 9) =
    Historical_Prefix_Value 3 (Units_Value 9)"
  by (simp_all add: historical_native_read_def native_history_read_value_def historical_fixture_prefixes_def
      native_resize_read_prefixes_def historical_project_value_def historical_fixture_projection_def)

lemma historical_g0_only_index_substitution_changes_the_old_value:
  "historical_native_read False True True 0 (historical_fixture_prefixes 0 9) =
    Historical_Prefix_Value 0 (Units_Value 0)"
  "historical_native_read True True True 0 (historical_fixture_prefixes 0 9) =
    Historical_Prefix_Value 0 (Units_Value 9)"
  "historical_native_read True True True 4 (historical_fixture_prefixes 0 9) = Product_Read_Unavailable"
  by (simp_all add: historical_native_read_def native_history_read_value_def historical_wrong_last_index_def
      historical_fixture_prefixes_def native_resize_read_prefixes_def historical_project_value_def
      historical_fixture_projection_def)

lemma historical_access_is_current_and_cannot_be_bypassed_by_an_old_prefix:
  "historical_native_read substitute False available requested prefixes = Product_Read_Rejected"
  "historical_native_read substitute True False requested prefixes = Product_Read_Unavailable"
  by (simp_all add: historical_native_read_def)

thm_oracles historical_native_resize_and_reference_recording_agree
  historical_read_reuses_exact_named_reference_prefix historical_query2_reuses_the_existing_service_selector
  historical_g0_old_unavailable_and_current historical_g0_each_named_prefix_keeps_its_visibility
  historical_g0_only_index_substitution_changes_the_old_value

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms historical_native_resize_and_reference_recording_agree
    historical_read_reuses_exact_named_reference_prefix historical_query2_reuses_the_existing_service_selector
    historical_g0_old_unavailable_and_current historical_g0_each_named_prefix_keeps_its_visibility
    historical_g0_only_index_substitution_changes_the_old_value})
  then () else error "Unexpected oracle in historical read G0"
\<close>

end
