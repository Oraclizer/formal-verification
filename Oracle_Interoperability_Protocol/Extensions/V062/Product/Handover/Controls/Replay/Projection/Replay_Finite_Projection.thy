theory Replay_Finite_Projection
  imports "OIP_V062_P13_Replay_Lookup.Replay_Receipt_Lookup"
    "OIP_Reference_Execution.Reference_Read_Code"
begin

text \<open>The finite reader indexes actual session and result rows. The
identity constants and typed verification are those of the source fixture.
The same typed payload is compared in full, including its original cut
and any credential. No test outcome is supplied to the reader.\<close>

record rpf_state =
  rpf_epoch :: nat
  rpf_revision :: nat
  rpf_live :: bool
  rpf_sessions :: "(product_session_id \<times> product_session_binding) list"
  rpf_entries :: "(client_call_id \<times> (product_result_entry \<times> bool)) list"
  rpf_completed :: "client_call_id list"

definition rpf_session_rows ::
  "product_session_id list \<Rightarrow> outcome_world \<Rightarrow> (product_session_id \<times> product_session_binding) list" where
  "rpf_session_rows keys outcomes = List.map_filter
    (\<lambda>key. map_option (Pair key) (product_sessions (product_durable (outcome_source outcomes)) key)) keys"

definition rpf_ready_entry ::
  "outcome_world \<Rightarrow> client_call_id \<Rightarrow> (product_result_entry \<times> bool) option" where
  "rpf_ready_entry outcomes key =
    map_option (\<lambda>entry. (entry,result_completion_ready entry outcomes)) (outcome_entries outcomes key)"

definition rpf_result_rows ::
  "client_call_id list \<Rightarrow> outcome_world \<Rightarrow> (client_call_id \<times> (product_result_entry \<times> bool)) list" where
  "rpf_result_rows keys outcomes =
    List.map_filter (\<lambda>key. map_option (Pair key) (rpf_ready_entry outcomes key)) keys"

definition rpf_project ::
  "product_session_id list \<Rightarrow> client_call_id list \<Rightarrow> outcome_world \<Rightarrow> rpf_state" where
  "rpf_project session_keys call_keys outcomes =
    (let source = outcome_source outcomes; cut = current_product_cut source
     in \<lparr>rpf_epoch = cut_authority_epoch cut, rpf_revision = cut_revision cut,
          rpf_live = (call_local_status (product_calls source) = Endpoint_Up),
          rpf_sessions = rpf_session_rows session_keys outcomes,
          rpf_entries = rpf_result_rows call_keys outcomes,
          rpf_completed = filter (\<lambda>key. key \<in> outcome_completed outcomes) call_keys\<rparr>)"

fun rpf_command_caller_matches where
  "rpf_command_caller_matches actor (Client_Protocol endpoint index intent) =
    (case intent_request intent of None \<Rightarrow> True | Some request \<Rightarrow> request_caller request = actor)"
| "rpf_command_caller_matches actor (Client_Regulatory endpoint index request) = (request_caller request = actor)"
| "rpf_command_caller_matches actor (Client_Terminal cert) = True"
| "rpf_command_caller_matches actor (Client_Publication key) = True"

definition rpf_access where
  "rpf_access payload state =
    (let envelope = payload_envelope payload in
       envelope_caller envelope = 7 \<and> rpf_command_caller_matches 7 (envelope_command envelope) \<and>
       map_of (rpf_sessions state) (envelope_session envelope) =
         Some \<lparr>session_principal = 7, session_epoch = rpf_epoch state\<rparr>)"

definition rpf_identity where
  "rpf_identity epoch payload state =
    (let envelope = payload_envelope payload in
       epoch = rpf_epoch state \<and> envelope_session envelope = 1 \<and>
       rpf_access payload state \<and> command_target envelope (envelope_command envelope) = 0)"

definition rpf_observe where
  "rpf_observe matches payload state =
    (if \<not> rpf_access payload state then Collection_Rejected
     else if \<not> rpf_live state then Collection_Waiting
     else case map_of (rpf_entries state) (7,1) of None \<Rightarrow> Collection_Waiting
       | Some (recorded,ready) \<Rightarrow> if \<not> matches (result_payload recorded) payload then Collection_Rejected
         else if ready then Collected (result_outcome recorded) else Collection_Waiting)"

definition rpf_read where
  "rpf_read epoch_test matches epoch payload state =
    (if epoch_test \<and> rpf_identity epoch payload state \<and> rpf_live state
     then Some (Observed_Ordinary_Result (rpf_observe matches payload state)) else None)"

lemma rpf_map_of_finite_rows:
  fixes lookup :: "'key \<Rightarrow> 'value option"
  shows "map_of (List.map_filter (\<lambda>key. map_option (Pair key) (lookup key)) keys) query =
    (if query \<in> set keys then lookup query else None)"
proof (induction keys)
  case Nil
  then show ?case by simp
next
  case (Cons key rest)
  then show ?case by (cases "lookup key"; cases "query = key"; simp)
qed

lemma rpf_caller_predicate_matches_the_claimed_callers:
  "rpf_command_caller_matches actor command =
    (\<forall>caller \<in> product_claimed_callers command. caller = actor)"
  by (cases command) (simp_all split: option.splits)

lemma rpf_access_is_the_typed_bound_identity:
  assumes "envelope_session (payload_envelope payload) \<in> set session_keys"
  shows "rpf_access payload (rpf_project session_keys call_keys outcomes) =
    result_access_bound pro_verified 7 (7,1) payload outcomes"
proof -
  let ?session = "envelope_session (payload_envelope payload)"
  have session: "map_of (rpf_sessions (rpf_project session_keys call_keys outcomes)) ?session =
    product_sessions (product_durable (outcome_source outcomes)) ?session"
    using assms by (simp add: rpf_project_def Let_def rpf_session_rows_def rpf_map_of_finite_rows)
  have epoch: "rpf_epoch (rpf_project session_keys call_keys outcomes) =
    cut_authority_epoch (current_product_cut (outcome_source outcomes))"
    by (simp add: rpf_project_def Let_def)
  show ?thesis
    unfolding rpf_access_def Let_def session epoch result_access_bound_def pro_verified_def product_identity_bound_def
    by (simp only: fst_conv simp_thms rpf_caller_predicate_matches_the_claimed_callers)
qed

lemma rpf_identity_is_the_public_receipt_identity_gate:
  assumes "envelope_session (payload_envelope payload) \<in> set session_keys"
  shows "rpf_identity epoch payload (rpf_project session_keys call_keys outcomes) =
    prp_receipt_without_signed_epoch epoch payload (outcome_source outcomes)"
proof -
  let ?projected = "rpf_project session_keys call_keys outcomes"
  let ?source = "outcome_source outcomes"
  let ?envelope = "payload_envelope payload"
  let ?epoch = "cut_authority_epoch (current_product_cut ?source)"
  let ?sessions = "product_sessions (product_durable ?source)"
  have access: "rpf_access payload ?projected =
    product_identity_bound 7 ((7,1)::client_call_id) ?envelope ?source"
    unfolding rpf_access_is_the_typed_bound_identity[OF assms] result_access_bound_def pro_verified_def
    by (simp only: simp_thms)
  have epoch_at_cut: "rpf_epoch ?projected = ?epoch"
    by (simp add: rpf_project_def Let_def)
  have current_session:
    "?sessions 1 = Some \<lparr>session_principal = 7, session_epoch = epoch\<rparr>"
    if same_session: "envelope_session ?envelope = 1" and same_epoch: "epoch = ?epoch"
      and admitted_identity: "product_identity_bound 7 ((7,1)::client_call_id) ?envelope ?source"
  proof -
    have bound_session: "?sessions (envelope_session ?envelope) =
      Some \<lparr>session_principal = 7, session_epoch = ?epoch\<rparr>"
      using admitted_identity unfolding product_identity_bound_def by blast
    show ?thesis
      unfolding same_epoch
      by (rule bound_session[unfolded same_session])
  qed
  have same_orientation: "((1::product_session_id) = envelope_session ?envelope) = (envelope_session ?envelope = 1)"
    by (rule eq_commute)
  have endpoint:
    "prp_receipt_without_signed_epoch epoch payload ?source =
      (epoch = ?epoch \<and> ?sessions 1 = Some \<lparr>session_principal = 7, session_epoch = epoch\<rparr> \<and>
       envelope_session ?envelope = 1 \<and> product_identity_bound 7 ((7,1)::client_call_id) ?envelope ?source \<and>
       command_target ?envelope (envelope_command ?envelope) = 0)"
    unfolding prp_receipt_without_signed_epoch_def endpoint_call_identity_def Let_def
      active_identity_def prp_authenticate_def prp_policy_def prp_verify_def identity_case_proof_def
      session_proof.select_convs same_orientation
    by (simp add: identity_case_directory_def identity_case_user_def conj_assoc)
  show ?thesis
    unfolding rpf_identity_def Let_def access epoch_at_cut endpoint
    using current_session by blast
qed

lemma rpf_lookup_is_the_public_observer:
  assumes "envelope_session (payload_envelope payload) \<in> set session_keys" "(7,1) \<in> set call_keys"
  shows "rpf_observe matches payload (rpf_project session_keys call_keys outcomes) =
    prc_observe_with_payload_test matches payload outcomes"
proof -
  have rows: "rpf_entries (rpf_project session_keys call_keys outcomes) = rpf_result_rows call_keys outcomes"
    by (simp add: rpf_project_def Let_def)
  have entries:
    "map_of (rpf_entries (rpf_project session_keys call_keys outcomes)) (7,1) = rpf_ready_entry outcomes (7,1)"
    unfolding rows rpf_result_rows_def rpf_map_of_finite_rows
    by (rule if_P[OF assms(2)])
  have live: "rpf_live (rpf_project session_keys call_keys outcomes) =
      (call_local_status (product_calls (outcome_source outcomes)) = Endpoint_Up)"
    by (simp add: rpf_project_def Let_def)
  show ?thesis
    unfolding rpf_observe_def prc_observe_with_payload_test_def
      rpf_access_is_the_typed_bound_identity[OF assms(1)] entries rpf_ready_entry_def live
    by (cases "outcome_entries outcomes (7,1)") simp_all
qed

lemma rpf_reader_is_the_public_retained_receipt:
  assumes "envelope_session (payload_envelope payload) \<in> set session_keys" "(7,1) \<in> set call_keys"
  shows "rpf_read epoch_test matches epoch payload (rpf_project session_keys call_keys (prc_outcomes s)) =
    prc_read_with_tests epoch_test matches epoch payload s"
proof -
  let ?outcomes = "prc_outcomes s"
  have available: "rpf_live (rpf_project session_keys call_keys ?outcomes) =
    (call_local_status (product_calls (outcome_source ?outcomes)) = Endpoint_Up)"
    by (simp add: rpf_project_def Let_def)
  show ?thesis
    unfolding rpf_read_def prc_read_with_tests_def rpf_identity_is_the_public_receipt_identity_gate[OF assms(1)]
      rpf_lookup_is_the_public_observer[OF assms] available
    by (rule refl)
qed

definition rpf_payload_for_duration where
  "rpf_payload_for_duration duration = prp_original_payload\<lparr>payload_envelope :=
    (payload_envelope prp_original_payload)\<lparr>envelope_command :=
      Client_Protocol 0 0 (Reserve_Intent (sample_request 17) [] duration)\<rparr>\<rparr>"

lemma rpf_duration_controls_change_the_actual_typed_payload:
  "rpf_payload_for_duration 10 = prp_original_payload"
  "rpf_payload_for_duration 11 = prp_changed_payload"
  by (simp_all add: rpf_payload_for_duration_def prp_changed_payload_def prp_original_payload_def hf_envelope_def hf_reserve_def)

definition rpf_prefix where
  "rpf_prefix source = capture_snapshot (call_authority_state (product_calls source))"

definition rpf_live_history_after_dispatch where
  "rpf_live_history_after_dispatch =
    (let start = current_product_cut hf_initial; reserved = current_product_cut hf_reserved;
         dispatched = current_product_cut hf_dispatched;
         history = initialize_reference_history (cut_authority_epoch start) (rpf_prefix hf_initial);
         first = record_reference_advance (cut_authority_epoch reserved)
           (cut_revision reserved - cut_revision start) (rpf_prefix hf_reserved) history
     in record_reference_advance (cut_authority_epoch dispatched)
        (cut_revision dispatched - cut_revision reserved) (rpf_prefix hf_dispatched) first)"

lemma rpf_read_prefixes_are_the_actual_revision_prefixes:
  "native_read_history_related (cut_authority_epoch (current_product_cut hf_dispatched))
    (cut_revision (current_product_cut hf_dispatched))
    [rpf_prefix hf_initial, rpf_prefix hf_reserved, rpf_prefix hf_dispatched]
    rpf_live_history_after_dispatch"
  by (simp add: rpf_live_history_after_dispatch_def Let_def native_read_history_related_def
      initialize_reference_history_def record_reference_advance_def
      prp_revisions_come_from_actual_submissions prp_initial_reserved_dispatched_metadata numeral_2_eq_2)

lemma rpf_current_and_history_keep_different_selection_rules:
  "native_current_read_value permitted read (current_product_cut hf_initial)
    (cut_authority_epoch (current_product_cut hf_dispatched)) (cut_revision (current_product_cut hf_dispatched))
    [rpf_prefix hf_initial, rpf_prefix hf_reserved, rpf_prefix hf_dispatched] = None"
  "native_history_read_value permitted read 0 [rpf_prefix hf_initial, rpf_prefix hf_reserved, rpf_prefix hf_dispatched] =
    (if permitted then Some (0, read (rpf_prefix hf_initial)) else None)"
  by (simp_all add: native_current_read_value_def native_history_read_value_def prp_revisions_come_from_actual_submissions)

thm_oracles rpf_reader_is_the_public_retained_receipt rpf_duration_controls_change_the_actual_typed_payload
  rpf_read_prefixes_are_the_actual_revision_prefixes rpf_current_and_history_keep_different_selection_rules

ML \<open>
  if null (Thm_Deps.all_oracles @{thms rpf_reader_is_the_public_retained_receipt
      rpf_duration_controls_change_the_actual_typed_payload
      rpf_read_prefixes_are_the_actual_revision_prefixes rpf_current_and_history_keep_different_selection_rules})
  then writeln "P13_REPLAY_FINITE_PROJECTION_ORACLES_EMPTY"
  else error "Unexpected oracle in finite replay projection"
\<close>

end
