theory Secondary_Read_G0
  imports "OIP_Message_Code.Wire_Code_Read_Service" "OIP_Reference_Execution.Reference_Read_Code"
begin

text \<open>
  Pure source projections after current exact-request authorization. No signature
  verifier or token issuer is replaced by a Boolean implementation. The authorized
  input summarizes external active identity, target registration, grant and exact
  signed request checks. Status target equality is consumed separately here.
  Terminal payloads remain polymorphic and are returned without modification.
\<close>

datatype 'answer secondary_read_reply =
    Secondary_Rejected | Secondary_Unavailable | Secondary_Answer 'answer

definition secondary_gate where
  "secondary_gate target_matches_input authorized_input available_input answer_input =
    (if \<not> target_matches_input \<or> \<not> authorized_input then Secondary_Rejected
     else if \<not> available_input then Secondary_Unavailable else Secondary_Answer answer_input)"

record 'payload secondary_slot =
  secondary_slot_terminal :: "'payload option"
  secondary_slot_publication :: bool

datatype ('transfer,'legal) secondary_terminal =
    Secondary_Transfer 'transfer | Secondary_Legal 'legal

record ('phase,'transfer,'legal) secondary_status_view =
  secondary_status_phase :: "'phase option"
  secondary_status_pending :: nat
  secondary_status_terminal :: "('transfer,'legal) secondary_terminal option"
  secondary_status_published :: bool

fun secondary_slot_decision :: "'payload secondary_slot option \<Rightarrow> 'payload option" where
  "secondary_slot_decision None = None"
| "secondary_slot_decision (Some slot_input) = secondary_slot_terminal slot_input"

fun secondary_slot_published :: "'payload secondary_slot option \<Rightarrow> bool" where
  "secondary_slot_published None = False"
| "secondary_slot_published (Some slot_input) = secondary_slot_publication slot_input"

definition secondary_terminal_select where
  "secondary_terminal_select transfer_input legal_input =
    (case secondary_slot_decision transfer_input of Some transfer_payload \<Rightarrow> Some (Secondary_Transfer transfer_payload)
     | None \<Rightarrow> map_option Secondary_Legal (secondary_slot_decision legal_input))"

definition secondary_status :: "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> source_key \<Rightarrow>
  'phase option \<Rightarrow> nat \<Rightarrow> 'transfer secondary_slot option \<Rightarrow> 'legal secondary_slot option \<Rightarrow>
  ('phase,'transfer,'legal) secondary_status_view secondary_read_reply" where
  "secondary_status authorized_input available_input requested_target requested_origin
      status_phase_input status_pending_input transfer_input legal_input =
    secondary_gate (fst requested_origin = requested_target) authorized_input available_input
      \<lparr>secondary_status_phase = status_phase_input, secondary_status_pending = status_pending_input,
       secondary_status_terminal = secondary_terminal_select transfer_input legal_input,
       secondary_status_published = (secondary_slot_published transfer_input \<or> secondary_slot_published legal_input)\<rparr>"

record secondary_journal_item =
  secondary_journal_id :: client_call_id
  secondary_journal_target :: nat
  secondary_journal_commit :: nat

definition secondary_journal where
  "secondary_journal current_namespace requested_target live_revision journal_rows =
    map secondary_journal_id (filter (\<lambda>entry_input.
      secondary_journal_target entry_input = requested_target \<and>
      fst (secondary_journal_id entry_input) = current_namespace \<and>
      secondary_journal_commit entry_input < live_revision) journal_rows)"

definition secondary_journal_nonstrict where
  "secondary_journal_nonstrict current_namespace requested_target live_revision journal_rows =
    map secondary_journal_id (filter (\<lambda>entry_input.
      secondary_journal_target entry_input = requested_target \<and>
      fst (secondary_journal_id entry_input) = current_namespace \<and>
      secondary_journal_commit entry_input \<le> live_revision) journal_rows)"

definition secondary_raw_application :: "nat \<Rightarrow> (nat option \<times> bool) list \<Rightarrow> nat option" where
  "secondary_raw_application selected_revision prefixes =
    (case native_history_read_value True fst selected_revision prefixes of None \<Rightarrow> None
     | Some (selected_index,raw_units) \<Rightarrow> raw_units)"

definition secondary_owner_registry :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat option" where
  "secondary_owner_registry registry_input selected_asset = map_of registry_input selected_asset"

lemma secondary_status_requires_its_origin_domain:
  "fst requested_origin \<noteq> requested_target \<Longrightarrow>
    secondary_status authorized available requested_target requested_origin phase_input pending_input transfer_input legal_input = Secondary_Rejected"
  by (simp add: secondary_status_def secondary_gate_def)

lemma secondary_transfer_terminal_has_priority:
  "secondary_slot_decision transfer_input = Some transfer_payload \<Longrightarrow>
    secondary_terminal_select transfer_input legal_input = Some (Secondary_Transfer transfer_payload)"
  by (simp add: secondary_terminal_select_def)

lemma secondary_legal_fallback_preserves_the_actual_payload:
  "secondary_slot_decision transfer_input = None \<Longrightarrow>
    secondary_terminal_select transfer_input legal_input = map_option Secondary_Legal (secondary_slot_decision legal_input)"
  by (simp add: secondary_terminal_select_def)

lemma secondary_transfer_only_reduces_to_the_old_projection:
  "secondary_terminal_select transfer_input None = map_option Secondary_Transfer (secondary_slot_decision transfer_input)"
  "(secondary_slot_published transfer_input \<or> secondary_slot_published None) = secondary_slot_published transfer_input"
  by (cases "secondary_slot_decision transfer_input"; simp add: secondary_terminal_select_def)+

lemma secondary_journal_returns_only_target_namespace_and_prior_commits:
  assumes "call_id \<in> set (secondary_journal current_namespace requested_target live_revision journal_rows)"
  shows "\<exists>entry_input \<in> set journal_rows.
    secondary_journal_id entry_input = call_id \<and>
    secondary_journal_target entry_input = requested_target \<and>
    fst call_id = current_namespace \<and> secondary_journal_commit entry_input < live_revision"
  using assms by (auto simp: secondary_journal_def)

lemma secondary_journal_reuses_old_filter_under_exact_source_relation:
  assumes "\<forall>entry_input \<in> set journal_rows.
    secondary_journal_commit entry_input < live_revision \<and>
    source_target (secondary_journal_id entry_input) = Some (secondary_journal_target entry_input)"
  shows "secondary_journal current_namespace requested_target live_revision journal_rows =
    filter (\<lambda>call_id. fst call_id = current_namespace \<and> source_target call_id = Some requested_target)
      (map secondary_journal_id journal_rows)"
  using assms by (induction journal_rows) (auto simp: secondary_journal_def split: if_splits)

lemma secondary_g0_signed_status_is_a_target_control:
  "secondary_status True True 2 (0,17) (None::nat option) 0
    (None::nat list secondary_slot option) (None::nat list secondary_slot option) = Secondary_Rejected"
  "secondary_status True True 0 (0,17) (None::nat option) 0
    (None::nat list secondary_slot option) (None::nat list secondary_slot option) =
    Secondary_Answer \<lparr>secondary_status_phase = None,secondary_status_pending = 0,
      secondary_status_terminal = None,secondary_status_published = False\<rparr>"
  by (simp_all add: secondary_status_def secondary_gate_def secondary_terminal_select_def)

text \<open>Both-kind slots are internal projection controls, not reachable product seeds.\<close>

lemma secondary_g0_priority_fallback_and_publication_or:
  "secondary_terminal_select
    (Some \<lparr>secondary_slot_terminal = Some ([11,12]::nat list),secondary_slot_publication = False\<rparr>)
    (Some \<lparr>secondary_slot_terminal = Some ([21,22]::nat list),secondary_slot_publication = True\<rparr>) =
    Some (Secondary_Transfer [11,12])"
  "secondary_terminal_select
    (Some \<lparr>secondary_slot_terminal = (None::nat list option),secondary_slot_publication = False\<rparr>)
    (Some \<lparr>secondary_slot_terminal = Some ([21,22]::nat list),secondary_slot_publication = True\<rparr>) =
    Some (Secondary_Legal [21,22])"
  "secondary_slot_published
    (Some \<lparr>secondary_slot_terminal = Some ([11,12]::nat list),secondary_slot_publication = False\<rparr>) \<or>
    secondary_slot_published
    (Some \<lparr>secondary_slot_terminal = Some ([21,22]::nat list),secondary_slot_publication = True\<rparr>)"
  by (simp_all add: secondary_terminal_select_def)

definition secondary_g0_journal_item where
  "secondary_g0_journal_item namespace_input sequence_input target_input commit_input =
    \<lparr>secondary_journal_id = (namespace_input,sequence_input),
     secondary_journal_target = target_input,secondary_journal_commit = commit_input\<rparr>"

definition secondary_g0_journal_seed where
  "secondary_g0_journal_seed = [secondary_g0_journal_item 7 1 2 0,
    secondary_g0_journal_item 7 2 2 1,secondary_g0_journal_item 7 3 2 2]"

lemma secondary_g0_journal_keeps_source_order:
  "secondary_journal 7 2 3 secondary_g0_journal_seed = [(7,1),(7,2),(7,3)]"
  by (simp add: secondary_journal_def secondary_g0_journal_seed_def secondary_g0_journal_item_def)

text \<open>A journal commit equal to live revision is an internal invariant control.\<close>

lemma secondary_g0_only_nonstrict_bound_exposes_the_equal_revision_item:
  "secondary_journal 7 2 3 [secondary_g0_journal_item 7 4 2 3] = []"
  "secondary_journal_nonstrict 7 2 3 [secondary_g0_journal_item 7 4 2 3] = [(7,4)]"
  by (simp_all add: secondary_journal_def secondary_journal_nonstrict_def secondary_g0_journal_item_def)

lemma secondary_g0_raw_ignores_lock_but_keeps_the_selected_prefix:
  "secondary_raw_application 2 [(Some (0::nat),False),(Some 0,True),(Some 9,True),(Some 9,False)] = Some 9"
  "secondary_raw_application 0 [(Some (0::nat),False),(Some 0,True),(Some 9,True),(Some 9,False)] = Some 0"
  "secondary_raw_application 4 [(Some (0::nat),False),(Some 0,True),(Some 9,True),(Some 9,False)] = None"
  by (simp_all add: secondary_raw_application_def native_history_read_value_def)

lemma secondary_g0_owner_is_exact_registry_lookup:
  "secondary_owner_registry [(17,7)] 17 = Some 7"
  "secondary_owner_registry [(17,7)] 18 = None"
  "secondary_owner_registry [(17,8)] 17 = Some 8"
  by (simp_all add: secondary_owner_registry_def)

lemma secondary_wire_status_keeps_the_origin_and_target_separate:
  assumes "wire_message_family core = Wire_Query" "wire_opcode (wire_operation_body core) = 4"
    "wire_words (wire_operation_body core) = [session_input,origin_domain,origin_event]"
    "wire_blobs (wire_operation_body core) = []" "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core = Some
    (Service_Read token \<lparr>proof_session = session_input,proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) (Operation_Status (origin_domain,origin_event)) None)"
  using assms by (simp add: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decode_wire_query_body_def parse_wire_application_query_def Let_def)

lemma secondary_wire_journal_keeps_the_session_and_target:
  assumes "wire_message_family core = Wire_Query" "wire_opcode (wire_operation_body core) = 5"
    "wire_words (wire_operation_body core) = [session_input]"
    "wire_blobs (wire_operation_body core) = []" "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core = Some
    (Service_Read token \<lparr>proof_session = session_input,proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) Authority_Journal None)"
  using assms by (simp add: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decode_wire_query_body_def Let_def)

lemma secondary_wire_raw_keeps_the_named_application_asset:
  assumes "wire_message_family core = Wire_Query" "wire_opcode (wire_operation_body core) = 3"
    "wire_words (wire_operation_body core) = [session_input,1,asset_input]"
    "wire_blobs (wire_operation_body core) = []" "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core = Some
    (Service_Read token \<lparr>proof_session = session_input,proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) (Raw_Data (Application_Value asset_input)) None)"
  using assms by (simp add: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decode_wire_query_body_def parse_wire_application_query_def Let_def)

lemma secondary_wire_owner_keeps_the_named_registry_asset:
  assumes "wire_message_family core = Wire_Query" "wire_opcode (wire_operation_body core) = 7"
    "wire_words (wire_operation_body core) = [session_input,asset_input]"
    "wire_blobs (wire_operation_body core) = []" "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core = Some
    (Service_Read token \<lparr>proof_session = session_input,proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) (Owner_Data asset_input) None)"
  using assms by (simp add: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decode_wire_query_body_def Let_def)

thm_oracles secondary_status_requires_its_origin_domain secondary_transfer_terminal_has_priority
  secondary_legal_fallback_preserves_the_actual_payload secondary_journal_returns_only_target_namespace_and_prior_commits
  secondary_journal_reuses_old_filter_under_exact_source_relation secondary_g0_signed_status_is_a_target_control
  secondary_g0_priority_fallback_and_publication_or secondary_g0_journal_keeps_source_order
  secondary_g0_only_nonstrict_bound_exposes_the_equal_revision_item
  secondary_g0_raw_ignores_lock_but_keeps_the_selected_prefix secondary_g0_owner_is_exact_registry_lookup
  secondary_wire_status_keeps_the_origin_and_target_separate secondary_wire_journal_keeps_the_session_and_target
  secondary_wire_raw_keeps_the_named_application_asset secondary_wire_owner_keeps_the_named_registry_asset

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms secondary_status_requires_its_origin_domain
    secondary_transfer_terminal_has_priority secondary_legal_fallback_preserves_the_actual_payload
    secondary_journal_returns_only_target_namespace_and_prior_commits
    secondary_journal_reuses_old_filter_under_exact_source_relation
    secondary_g0_signed_status_is_a_target_control secondary_g0_priority_fallback_and_publication_or
    secondary_g0_journal_keeps_source_order secondary_g0_only_nonstrict_bound_exposes_the_equal_revision_item
    secondary_g0_raw_ignores_lock_but_keeps_the_selected_prefix secondary_g0_owner_is_exact_registry_lookup
    secondary_wire_status_keeps_the_origin_and_target_separate secondary_wire_journal_keeps_the_session_and_target
    secondary_wire_raw_keeps_the_named_application_asset secondary_wire_owner_keeps_the_named_registry_asset})
  then () else error "Unexpected oracle in secondary read G0"
\<close>

end
