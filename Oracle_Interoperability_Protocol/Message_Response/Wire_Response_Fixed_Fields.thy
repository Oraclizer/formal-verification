theory Wire_Response_Fixed_Fields
  imports "OIP_Message_Code.Wire_Code_Response_Outcome"
    "OIP_Message_Code.Wire_Code_Response_Assembly"
    "OIP_Message_Code.Wire_Code_Response_Preflight"
begin

record response_fixed_channel =
  response_channel_profile :: negotiated_wire_profile
  response_channel_deployment :: nat
  response_channel_local :: nat
  response_channel_remote :: nat
  response_channel_expires :: nat
  response_channel_local_key :: wire_bytes
  response_channel_remote_key :: wire_bytes

record response_fixed_parameters =
  response_parameter_principal :: nat
  response_parameter_key :: nat
  response_parameter_epoch :: nat
  response_parameter_issued :: nat
  response_parameter_ttl :: nat
  response_parameter_uuid :: wire_bytes
  response_parameter_route :: nat

definition response_fixed_descriptor :: "nat \<Rightarrow> (reference_response_kind \<times> bool) option" where
  "response_fixed_descriptor number =
    (if number \<in> {1,2,3,4} \<union> {30..38} then Some (Recorded_Result,False)
     else if number \<in> {10..28} then Some (Recorded_Result,True)
     else if number \<in> {50..56} then Some (Delivery_Refusal,False)
     else if number \<in> {70..77} then Some (Validation_Refusal,False) else None)"

lemma response_fixed_descriptor_is_the_literal_source_kind_commit_table:
  "response_fixed_descriptor number = Some (kind,committed) \<longleftrightarrow>
    number \<in> reference_result_codes kind committed"
  unfolding response_fixed_descriptor_def reference_result_codes_def
  by (cases kind; cases committed; auto; arith)

datatype response_fixed_observation =
    Response_Fixed_Received code_source_action_reply "code_source_receipt option"
  | Response_Fixed_Resolved code_source_resolution
  | Response_Fixed_Error code_source_wire_error

fun response_fixed_result :: "response_fixed_observation \<Rightarrow> (nat \<times> nat option)" where
  "response_fixed_result (Response_Fixed_Received reply retained) = code_source_from_received reply retained"
| "response_fixed_result (Response_Fixed_Resolved result) = code_source_from_resolution result"
| "response_fixed_result (Response_Fixed_Error error) = code_source_error_result error"

definition response_fixed_words where
  "response_fixed_words call_id result =
    (case result of (number,position) \<Rightarrow>
       case response_fixed_descriptor number of None \<Rightarrow> None | Some (kind,needs_commit) \<Rightarrow>
         if needs_commit \<noteq> (position \<noteq> None) then None
         else map_option (\<lambda>words. (kind,number,position,words))
           (code_response_words call_id kind number position))"

lemma response_fixed_words_keep_the_actual_position_without_replacing_it_by_a_cut:
  assumes "response_fixed_words call_id (number,position) = Some (kind,actual_number,actual_position,words)"
  shows "actual_number = number" "actual_position = position"
    "code_response_words call_id kind number position = Some words"
    "response_fixed_descriptor number = Some (kind,position \<noteq> None)"
  using assms by (auto simp: response_fixed_words_def split: option.splits prod.splits if_splits)

lemma response_fixed_parsed_words_reconstruct_the_actual_response_body:
  assumes "response_result_words words = Some (call_id,kind,number,position)"
  shows "words = wire_words (reference_response_body call_id kind number position original)"
  using assms by (cases call_id; cases kind; cases position)
    (auto simp: response_result_words_def response_kind_at_def reference_response_body_def
      split: list.splits option.splits if_splits)

lemma response_fixed_matching_debit_receipt_keeps_the_retained_commit:
  "response_fixed_result (Response_Fixed_Received (Code_Source_Ordinary_Collected stored)
      (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected stored)))) =
    (code_source_ordinary_number (source_outcome_reply stored),source_outcome_commit stored)"
  by (simp add: code_source_ordinary_result_def)

lemma response_fixed_mismatched_receipt_is_not_a_result_supplier:
  "actual \<noteq> retained \<Longrightarrow>
    response_fixed_result (Response_Fixed_Received (Code_Source_Ordinary_Collected actual)
      (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected retained)))) = (50,None)"
  by simp

definition response_fixed_atomicity where
  "response_fixed_atomicity channel =
    (let modes = negotiated_atomicities (response_channel_profile channel) in
     if finite modes \<and> modes \<noteq> {} then Some (Min modes) else None)"

lemma response_fixed_atomicity_is_the_first_member_of_the_finite_source_set:
  assumes "response_fixed_atomicity channel = Some mode"
  shows "mode \<in> negotiated_atomicities (response_channel_profile channel)"
    "\<forall>other \<in> negotiated_atomicities (response_channel_profile channel). mode \<le> other"
proof -
  let ?modes = "negotiated_atomicities (response_channel_profile channel)"
  have selected: "finite ?modes \<and> ?modes \<noteq> {} \<and> mode = Min ?modes"
    using assms by (auto simp: response_fixed_atomicity_def Let_def split: if_splits)
  have finite_modes: "finite ?modes" by (rule conjunct1[OF selected])
  have nonempty_modes: "?modes \<noteq> {}" using selected by blast
  have actual_minimum: "mode = Min ?modes" using selected by blast
  show "mode \<in> ?modes"
    unfolding actual_minimum by (rule Min_in[OF finite_modes nonempty_modes])
  show "\<forall>other \<in> ?modes. mode \<le> other"
  proof (intro ballI)
    fix other
    assume member: "other \<in> ?modes"
    show "mode \<le> other"
      unfolding actual_minimum by (rule Min_le[OF finite_modes member])
  qed
qed

definition response_fixed_core ::
  "response_fixed_channel \<Rightarrow> response_fixed_parameters \<Rightarrow> nat \<Rightarrow>
    nat list \<Rightarrow> wire_bytes \<Rightarrow> wire_core" where
  "response_fixed_core channel parameters atomicity words original =
    \<lparr>wire_version = 6,wire_purpose = 1,
     wire_deployment = response_channel_deployment channel,
     wire_source_domain = response_channel_local channel,wire_target_domain = response_channel_remote channel,
     wire_principal = response_parameter_principal parameters,wire_key_number = response_parameter_key parameters,
     wire_authority_epoch = response_parameter_epoch parameters,wire_sent_seconds = response_parameter_issued parameters,
     wire_ttl_seconds = response_parameter_ttl parameters,wire_uuid = response_parameter_uuid parameters,
     wire_message_family = Wire_Ack,wire_primary_code = 1,wire_secondary_code = None,wire_signature_scheme = 1,
     wire_operation_body = \<lparr>wire_opcode = 2,wire_words = words,wire_blobs = [original],wire_deadline = Deadline_Absent\<rparr>,
     wire_atomicity = atomicity,wire_priority = 3,wire_route_scope = response_parameter_route parameters\<rparr>"

lemma response_fixed_core_has_no_caller_selected_outer_header:
  "wire_deployment (response_fixed_core channel parameters atomicity words original) = response_channel_deployment channel"
  "wire_source_domain (response_fixed_core channel parameters atomicity words original) = response_channel_local channel"
  "wire_target_domain (response_fixed_core channel parameters atomicity words original) = response_channel_remote channel"
  "wire_principal (response_fixed_core channel parameters atomicity words original) = response_parameter_principal parameters"
  "wire_key_number (response_fixed_core channel parameters atomicity words original) = response_parameter_key parameters"
  "wire_authority_epoch (response_fixed_core channel parameters atomicity words original) = response_parameter_epoch parameters"
  "wire_blobs (wire_operation_body (response_fixed_core channel parameters atomicity words original)) = [original]"
  by (simp_all add: response_fixed_core_def)

lemma response_fixed_core_is_the_existing_source_constructor_with_fixed_getters:
  "response_fixed_core channel parameters atomicity words original =
    code_response_core (response_fixed_core channel parameters atomicity [] []) atomicity words original"
  by (simp add: response_fixed_core_def code_response_core_def)

text \<open>
  Rust anchors: response.rs response_words/response_atomicity/response_core.
  The source Outcome/CommitRef is data supplied by the actual retained consumer,
  not a commit guessed from an input cut. The literal source descriptor and
  optional position are checked here. Finite sets are the value domain of the
  source BTreeSet; no alternate atomicity picker or arbitrary outer core is used.
\<close>

end
