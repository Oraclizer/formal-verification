theory Wire_Code_Read_Service
  imports Wire_Code_Operands_Metadata "OIP_Product.Recovery_Service"
begin

fun code_read_invocation_service :: "'token wire_read_invocation \<Rightarrow> 'token retained_service_action" where
  "code_read_invocation_service (Invoke_Authenticated_Read token session_auth target request) =
    Service_Read token session_auth target request None"
| "code_read_invocation_service (Invoke_Authenticated_Capture token session_auth target query) =
    Service_Capture token session_auth target query"

definition code_source_nonreceipt_read_service :: "'token \<Rightarrow> wire_core \<Rightarrow> 'token retained_service_action option" where
  "code_source_nonreceipt_read_service token core =
    (case code_decode_query_nonreceipt core of None \<Rightarrow> None
     | Some (Wire_Read_Request session_auth request) \<Rightarrow>
         Some (Service_Read token session_auth (wire_target_domain core) request None)
     | Some (Wire_Cache_Request session_auth query) \<Rightarrow>
         Some (Service_Capture token session_auth (wire_target_domain core) query))"

theorem a_source_read_uses_the_existing_exact_authenticated_invocation:
  assumes "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core =
    map_option code_read_invocation_service (decoded_wire_read_action token core)"
  using assms by (cases "decode_wire_query_body core")
    (auto simp: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decoded_wire_read_action_def split: parsed_wire_query.splits)

lemma a_current_source_application_query_keeps_the_session_epoch_cut_and_asset:
  assumes "wire_message_family core = Wire_Query"
    "wire_opcode (wire_operation_body core) = 1"
    "wire_words (wire_operation_body core) = [session,revision,1,asset]"
    "wire_blobs (wire_operation_body core) = []"
    "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core = Some
    (Service_Read token \<lparr>proof_session = session,proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) (Current_Data (Application_Value asset)
        \<lparr>cut_authority_epoch = wire_authority_epoch core,cut_revision = revision\<rparr>) None)"
proof -
  have old: "decoded_wire_read_action token core = Some
      (Invoke_Authenticated_Read token \<lparr>proof_session = session,proof_epoch = wire_authority_epoch core\<rparr>
        (wire_target_domain core) (Current_Data (Application_Value asset)
          \<lparr>cut_authority_epoch = wire_authority_epoch core,cut_revision = revision\<rparr>))"
    by (rule an_encoded_current_query_supplies_the_actual_session_cut_and_asset[OF assms(1,2,3,4)])
  show ?thesis using a_source_read_uses_the_existing_exact_authenticated_invocation[OF assms(5), of token] old by simp
qed

definition code_nonreceipt_read_allowed where
  "code_nonreceipt_read_allowed profile core \<longleftrightarrow> code_decode_query_nonreceipt core \<noteq> None"

definition code_select_nonreceipt_read_service where
  "code_select_nonreceipt_read_service verify attest scope token bytes =
    (case code_library_gate verify attest code_nonreceipt_read_allowed scope bytes of
       Gate_Refused reason \<Rightarrow> None
     | Gate_Admitted packet \<Rightarrow> code_source_nonreceipt_read_service token (packet_core packet))"

context source_attestation
begin

theorem the_prechecked_source_read_selector_is_the_existing_product_service_selector:
  assumes profile: "negotiated_version (boundary_profile scope) = 6"
    and precheck: "code_check_declared_version bytes (boundary_max_frame scope) = None"
    and threshold: "\<not> boundary_threshold_supported scope"
  shows "code_select_nonreceipt_read_service verify attest scope token bytes =
    service_action_from_wire verify attest code_nonreceipt_read_allowed scope
      (code_source_nonreceipt_read_service token) bytes"
proof -
  have gate: "code_library_gate verify attest code_nonreceipt_read_allowed scope bytes =
      wire_gate verify attest code_nonreceipt_read_allowed scope bytes"
    by (rule prechecked_current_input_reuses_the_model_admission[OF profile precheck threshold])
  show ?thesis using gate
    by (cases "wire_gate verify attest code_nonreceipt_read_allowed scope bytes")
      (simp_all add: code_select_nonreceipt_read_service_def service_action_from_wire_def)
qed

theorem the_source_read_service_consumes_only_the_received_canonical_core:
  assumes profile: "negotiated_version (boundary_profile scope) = 6"
    and precheck: "code_check_declared_version bytes (boundary_max_frame scope) = None"
    and threshold: "\<not> boundary_threshold_supported scope"
    and selected: "code_select_nonreceipt_read_service verify attest scope token bytes = Some action"
  obtains packet :: wire_packet
  where "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "code_source_nonreceipt_read_service token (packet_core packet) = Some action"
    "current_wire_scope scope (packet_core packet)"
proof -
  have link: "code_select_nonreceipt_read_service verify attest scope token bytes =
      service_action_from_wire verify attest code_nonreceipt_read_allowed scope
        (code_source_nonreceipt_read_service token) bytes"
    by (rule the_prechecked_source_read_selector_is_the_existing_product_service_selector
      [OF profile precheck threshold, where verify=verify and attest=attest and token=token])
  have actual: "service_action_from_wire verify attest code_nonreceipt_read_allowed scope
      (code_source_nonreceipt_read_service token) bytes = Some action"
    by (rule trans[OF link[symmetric] selected])
  obtain packet where exact:
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
    "code_source_nonreceipt_read_service token (packet_core packet) = Some action"
    "current_wire_scope scope (packet_core packet)"
    by (rule admitted_canonical_bytes_are_the_only_input_to_the_selected_product_service[OF actual])
  show thesis by (rule that[OF exact])
qed

end

text \<open>
  Source wire.rs query_at/read_at and run_operand nonreceipt read branch.
  Service_Read uses no supplied cache; Capture has its distinct existing
  Service_Capture constructor. Query8 receipt, ordered nested Debit rejection
  and live product identity/receipt execution are separate consumers.
\<close>

end
