theory Wire_Code_Finite_Raw_Ordinary
  imports Wire_Code_Finite_Closed_Check
begin

definition code_finite_model_binding_from_native :: "nat \<Rightarrow> nat \<Rightarrow> wire_native_call \<Rightarrow> transfer_binding" where
  "code_finite_model_binding_from_native model_epoch separator native =
    \<lparr>binding_key = native_origin native,binding_asset = native_asset native,binding_amount = native_amount native,
     binding_destination = native_destination native,binding_recipient = native_recipient native,
     binding_source_epoch = model_epoch,binding_operation = Destination_Credit,binding_separator = separator\<rparr>"

definition code_finite_model_request_from_native :: "code_finite_lock_context \<Rightarrow> wire_native_call \<Rightarrow>
  transfer_binding \<Rightarrow> execution_request" where
  "code_finite_model_request_from_native descriptor native binding =
    \<lparr>request_binding = binding,
     request_certificate = \<lparr>certificate_statement = \<lparr>statement_binding = binding,statement_status = Observed\<rparr>,
       certificate_epoch = native_origin_epoch native,certificate_signers = [],certificate_signature = 0\<rparr>,
     request_caller = fst (native_id native),request_authority_epoch = cut_authority_epoch (native_cut native),
     request_version = finite_context_version descriptor\<rparr>"

fun code_finite_three_command :: "ordinary_wire_command \<Rightarrow> code_finite_financial_command option" where
  "code_finite_three_command (Wire_Reserve duration) = Some (Code_Finite_Reserve duration)"
| "code_finite_three_command (Wire_Dispatch generation) = Some (Code_Finite_Dispatch generation)"
| "code_finite_three_command (Wire_Debit generation) = Some (Code_Finite_Debit generation)"
| "code_finite_three_command command = None"

record code_finite_selected_ordinary =
  finite_selected_core :: wire_core
  finite_selected_native :: wire_native_call
  finite_selected_payload :: code_source_call_payload
  finite_selected_request :: execution_request
  finite_selected_versions :: "(nat \<times> nat) list"
  finite_selected_command :: code_finite_financial_command

datatype code_finite_raw_selection =
    Code_Finite_Raw_Refused wire_refusal
  | Code_Finite_Raw_Pending
  | Code_Finite_Raw_Selected code_finite_selected_ordinary

definition code_finite_select_raw_ordinary :: "nat \<Rightarrow> code_finite_lock_context \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  wire_bytes \<Rightarrow> code_finite_raw_selection" where
  "code_finite_select_raw_ordinary frame_limit descriptor model_epoch separator bytes =
    (if length bytes > frame_limit then Code_Finite_Raw_Refused Invalid_Wire_Format
     else case code_check_declared_version bytes frame_limit of Some reason \<Rightarrow> Code_Finite_Raw_Refused reason
      | None \<Rightarrow> (case decode_wire_packet bytes of None \<Rightarrow> Code_Finite_Raw_Refused Invalid_Wire_Format | Some packet \<Rightarrow>
        let core = packet_core packet in
        if \<not> ((wire_message_family core = Wire_Lock \<and> wire_opcode (wire_operation_body core) \<in> {1,2}) \<or>
                  (wire_message_family core = Wire_State_Sync \<and> wire_opcode (wire_operation_body core) = 1))
        then Code_Finite_Raw_Pending
        else (case code_decode_ordinary core of Code_Ordinary_Refused reason \<Rightarrow> Code_Finite_Raw_Refused reason
         | Code_Ordinary_Ready native credential versions command \<Rightarrow>
           (case code_finite_three_command command of None \<Rightarrow> Code_Finite_Raw_Pending | Some selected \<Rightarrow>
             Code_Finite_Raw_Selected \<lparr>finite_selected_core = core,finite_selected_native = native,
               finite_selected_payload = code_source_payload_from_native core native credential versions command,
               finite_selected_request = code_finite_model_request_from_native descriptor native
                 (code_finite_model_binding_from_native model_epoch separator native),
               finite_selected_versions = versions,finite_selected_command = selected\<rparr>))))"

lemma a_fixed_finite_model_request_keeps_the_exact_native_caller_and_current_context_coordinate:
  "request_caller (code_finite_model_request_from_native descriptor native binding) = fst (native_id native)"
  "request_authority_epoch (code_finite_model_request_from_native descriptor native binding) = cut_authority_epoch (native_cut native)"
  "request_version (code_finite_model_request_from_native descriptor native binding) = finite_context_version descriptor"
  "request_binding (code_finite_model_request_from_native descriptor native binding) = binding"
  by (simp_all add: code_finite_model_request_from_native_def)

theorem a_raw_finite_selection_has_only_the_received_packet_and_fixed_source_request:
  assumes selected: "code_finite_select_raw_ordinary frame_limit descriptor model_epoch separator bytes = Code_Finite_Raw_Selected chosen"
  obtains packet :: wire_packet and native :: wire_native_call and credential versions command
  where "decode_wire_packet bytes = Some packet"
    "code_decode_ordinary (packet_core packet) = Code_Ordinary_Ready native credential versions command"
    "code_finite_three_command command = Some (finite_selected_command chosen)"
    "finite_selected_core chosen = packet_core packet" "finite_selected_native chosen = native"
    "finite_selected_payload chosen = code_source_payload_from_native (packet_core packet) native credential versions command"
    "finite_selected_request chosen = code_finite_model_request_from_native descriptor native
       (code_finite_model_binding_from_native model_epoch separator native)"
    "finite_selected_versions chosen = versions"
  using selected
  by (auto simp: code_finite_select_raw_ordinary_def Let_def
    split: option.splits code_ordinary_result.splits if_splits)

lemma a_finite_raw_selector_never_accepts_a_replacement_request_from_its_caller:
  assumes selected: "code_finite_select_raw_ordinary frame_limit descriptor model_epoch separator bytes = Code_Finite_Raw_Selected chosen"
  shows "source_payload_binding (finite_selected_payload chosen) = code_source_binding_from_native (finite_selected_native chosen)"
    "source_payload_caller (finite_selected_payload chosen) = fst (native_id (finite_selected_native chosen))"
    "source_payload_cut (finite_selected_payload chosen) = native_cut (finite_selected_native chosen)"
  using selected
  by (auto simp: code_finite_select_raw_ordinary_def code_source_payload_from_native_def Let_def
    split: option.splits code_ordinary_result.splits if_splits)

text \<open>
  The raw producer takes packet bytes, not a supplied typed action/decoder.
  Native origin epoch remains in the full source payload. Model-only binding
  epoch/separator and context version are explicit coordinates; no equality
  to a newly signed source field is silently introduced. This selector is
  restricted to the first three financial commands. Other valid operation
  families remain Pending. Current external authentication/ingress checks,
  exact source credentials/owner balances and retained-call ordering are
  separate consumers, not new boolean success arguments here.
\<close>

end
