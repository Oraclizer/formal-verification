theory Handover_Seed_Frame
  imports "OIP_Reference_Execution.Reference_Signed_Handover_Code"
    "OIP_Product.Identity_Examples"
begin

text \<open>The first two handover rows use the actual typed setup prefix:
bootstrap balance 10, then Reserve, Dispatch, Source. Their input field
source_balance=5 is not used as an initial balance. The existing sample has
an additional unrelated account; the equality below is to the public seed,
and native correspondence is limited to the declared asset/account frame.\<close>

definition hf_sessions :: "nat \<Rightarrow> product_session_id \<Rightarrow> product_session_binding option" where
  "hf_sessions epoch session =
    (if session \<in> {1,2} then Some \<lparr>session_principal = 7, session_epoch = epoch\<rparr>
     else if session = 4 then Some \<lparr>session_principal = 8, session_epoch = epoch\<rparr> else None)"

definition hf_initial :: product_world where
  "hf_initial = (lock_example_world sample_initial)\<lparr>product_durable :=
    (product_durable (lock_example_world sample_initial))\<lparr>
      product_owners := (\<lambda>asset. if asset = 17 then Some 7 else None),
      product_sessions := hf_sessions 9\<rparr>\<rparr>"

definition hf_reserve :: client_command where
  "hf_reserve = Client_Protocol 0 0 (Reserve_Intent (sample_request 17) [] 10)"

definition hf_dispatch :: client_command where
  "hf_dispatch = Client_Protocol 0 0 (Dispatch_Intent (sample_request 17) 0 [])"

definition hf_debit :: client_command where
  "hf_debit = Client_Protocol 0 0 (Source_Intent (sample_request 17) 0 [])"

definition hf_envelope :: "nat \<Rightarrow> nat \<Rightarrow> client_command \<Rightarrow> product_world \<Rightarrow> product_envelope" where
  "hf_envelope session sequence command source = \<lparr>envelope_message = sequence,
    envelope_origin = (0,17), envelope_asset = 17, envelope_caller = 7,
    envelope_session = session, envelope_cut = current_product_cut source,
    envelope_command = command\<rparr>"

definition hf_submit :: "nat \<Rightarrow> nat \<Rightarrow> client_command \<Rightarrow> product_world \<Rightarrow> product_world" where
  "hf_submit session sequence command source = sample.product_submit (\<lambda>_ _ _. True)
    7 (7,sequence) (hf_envelope session sequence command source) source"

definition hf_reserved :: product_world where
  "hf_reserved = hf_submit 1 1 hf_reserve hf_initial"

definition hf_dispatched :: product_world where
  "hf_dispatched = hf_submit 2 2 hf_dispatch hf_reserved"

definition hf_source :: product_world where
  "hf_source = hf_submit 2 3 hf_debit hf_dispatched"

definition hf_call_word :: "product_public_action list" where
  "hf_call_word = [Begin_Call (7,1) hf_reserve, Dispatch_Call (7,1) hf_reserve,
    Begin_Call (7,2) hf_dispatch, Dispatch_Call (7,2) hf_dispatch,
    Begin_Call (7,3) hf_debit, Dispatch_Call (7,3) hf_debit]"

definition hf_calls :: product_call_machine where
  "hf_calls = sample.finality_calls.run_calls hf_call_word (initial_call_machine finality_sample_initial)"

lemmas hf_setup_defs = hf_source_def hf_dispatched_def hf_reserved_def hf_submit_def
  hf_envelope_def hf_initial_def hf_sessions_def hf_reserve_def hf_dispatch_def hf_debit_def
  lock_example_world_def lock_example_core_def lock_example_contexts_def
  finality_sample_initial_def sample_initial_def initial_finality_core_def initial_call_machine_def
  sample.product_submit_def sample.product_apply_public_def
  product_new_call_def product_prior_call_def product_identity_bound_def current_product_cut_def
  sample.finality_calls.call_definitions Let_def

lemma hf_initial_call_machine:
  "product_calls hf_initial = initial_call_machine finality_sample_initial"
proof -
  have contexts: "lock_example_contexts =
    (\<lambda>endpoint. if endpoint = 0 then sample_source_context ACTIVE else sample_context ACTIVE)"
    by (rule ext) (simp add: lock_example_contexts_def)
  show ?thesis
    by (simp add: hf_initial_def lock_example_world_def lock_example_core_def contexts
        sample_initial_def finality_sample_initial_def initial_finality_core_def)
qed

lemma hf_reserve_is_a_fresh_call:
  "product_new_call 7 (7,1) (hf_envelope 1 1 hf_reserve hf_initial) hf_initial"
  by (simp add: hf_setup_defs sample_request_def)

lemma hf_dispatch_is_a_fresh_call:
  "product_new_call 7 (7,2) (hf_envelope 2 2 hf_dispatch hf_reserved) hf_reserved"
  by (simp add: hf_setup_defs sample_request_def)

lemma hf_debit_is_a_fresh_call:
  "product_new_call 7 (7,3) (hf_envelope 2 3 hf_debit hf_dispatched) hf_dispatched"
  by (simp add: hf_setup_defs sample_request_def)

lemma hf_a_fresh_submit_uses_the_checked_dispatch:
  assumes "product_new_call 7 (7,sequence) (hf_envelope session sequence command source) source"
  shows "product_calls (hf_submit session sequence command source) =
    sample.finality_calls.run_calls [Begin_Call (7,sequence) command, Dispatch_Call (7,sequence) command]
      (product_calls source)"
  unfolding hf_submit_def
  using sample.product_new_call_uses_authoritative_dispatch[OF TrueI assms]
  by (simp add: hf_envelope_def)

lemma hf_three_actual_submissions_produce_the_public_call_word:
  "product_calls hf_source = hf_calls"
proof -
  have reserved: "product_calls hf_reserved = sample.finality_calls.run_calls
      [Begin_Call (7,1) hf_reserve, Dispatch_Call (7,1) hf_reserve] (product_calls hf_initial)"
    unfolding hf_reserved_def
    by (rule hf_a_fresh_submit_uses_the_checked_dispatch[OF hf_reserve_is_a_fresh_call])
  have dispatched: "product_calls hf_dispatched = sample.finality_calls.run_calls
      [Begin_Call (7,2) hf_dispatch, Dispatch_Call (7,2) hf_dispatch] (product_calls hf_reserved)"
    unfolding hf_dispatched_def
    by (rule hf_a_fresh_submit_uses_the_checked_dispatch[OF hf_dispatch_is_a_fresh_call])
  have debited: "product_calls hf_source = sample.finality_calls.run_calls
      [Begin_Call (7,3) hf_debit, Dispatch_Call (7,3) hf_debit] (product_calls hf_dispatched)"
    unfolding hf_source_def
    by (rule hf_a_fresh_submit_uses_the_checked_dispatch[OF hf_debit_is_a_fresh_call])
  show ?thesis
    by (simp only: debited dispatched reserved hf_initial_call_machine hf_calls_def hf_call_word_def
        sample.finality_calls.run_calls.simps)
qed

lemma hf_call_word_uses_the_existing_checked_financial_prefix:
  "call_authority_state hf_calls = finality_sample_source 17"
  by (simp add: hf_calls_def hf_call_word_def hf_reserve_def hf_dispatch_def hf_debit_def
      initial_call_machine_def sample.finality_calls.call_definitions
      sample.first_protocol_call_uses_the_current_core finality_sample_source_def
      finality_sample_prefix_def finality_sample_initial_def initial_finality_core_def
      numeral_2_eq_2 numeral_3_eq_3 Let_def)

lemma hf_calls_have_three_commits_and_remain_available:
  "length (call_authority_log hf_calls) = 3"
  "call_local_status hf_calls = Endpoint_Up"
  "call_connection hf_calls = Authority_Connected"
  by (simp_all add: hf_calls_def hf_call_word_def initial_call_machine_def
      sample.finality_calls.call_definitions numeral_2_eq_2 numeral_3_eq_3 Let_def)

lemma hf_current_cut_is_derived_from_the_prefix:
  "current_product_cut hf_source = \<lparr>cut_authority_epoch = 9, cut_revision = 3\<rparr>"
  using hf_three_actual_submissions_produce_the_public_call_word hf_calls_have_three_commits_and_remain_available(1)
  by (simp add: current_product_cut_def hf_setup_defs sample_request_def numeral_3_eq_3)

lemma hf_source_keeps_the_three_actual_session_bindings:
  "product_sessions (product_durable hf_source) = hf_sessions 9"
  "owner_of_product hf_source 17 = Some 7"
  by (simp_all add: hf_setup_defs owner_of_product_def sample_request_def)

lemma hf_financial_seed_is_the_checked_pending_state:
  "authoritative_reservation_state hf_source =
    machine_state (core_parent (finality_sample_source 17))"
  by (simp add: authoritative_reservation_state_def
      hf_three_actual_submissions_produce_the_public_call_word
      hf_call_word_uses_the_existing_checked_financial_prefix)

lemma hf_initial_source_amount_is_ten:
  "source_units (authoritative_reservation_state hf_initial) (0,17) = 10"
  by (simp add: hf_initial_def authoritative_reservation_state_def lock_example_world_def
      lock_example_core_def initial_call_machine_def sample_initial_def
      initial_reservation_machine_def initial_reservation_state_def sample_balances_def)

lemma hf_pending_projection_is_derived_without_reading_expected_columns:
  "source_units (authoritative_reservation_state hf_source) (0,17) = 5"
  "sample_binding 17 \<in> example.unresolved_source_obligations (authoritative_reservation_state hf_source)"
  "destination_units (authoritative_reservation_state hf_source) (2,17,3) = 0"
  using sample.source_debit_puts_five_into_pending
  by (simp_all add: hf_financial_seed_is_the_checked_pending_state)

lemma hf_financial_frame_matches_the_existing_handover_seed:
  "authoritative_reservation_state hf_source = authoritative_reservation_state handover_case_source"
  unfolding hf_financial_seed_is_the_checked_pending_state
  by (simp add: handover_case_source_def terminal_example_world_def
      authoritative_reservation_state_def initial_call_machine_def Let_def)

lemma hf_source_phase_is_pending:
  "\<exists>claim. reservation_at (authoritative_reservation_state hf_source) (0,17) = Some claim \<and>
    reservation_binding claim = sample_binding 17 \<and> reservation_phase claim = Source_Pending"
proof -
  obtain claim where live: "recoverable_reservation handover_case_source (0,17) = Some claim"
    and binding: "reservation_binding claim = sample_binding 17"
    and phase: "reservation_phase claim = Source_Pending"
    using handover_case_retains_a_live_reservation by blast
  have stored: "reservation_at (authoritative_reservation_state handover_case_source) (0,17) = Some claim"
    using live by (auto simp: recoverable_reservation_def split: option.splits if_splits)
  show ?thesis
    unfolding hf_financial_frame_matches_the_existing_handover_seed
    using stored binding phase by blast
qed

thm_oracles hf_three_actual_submissions_produce_the_public_call_word
  hf_call_word_uses_the_existing_checked_financial_prefix hf_current_cut_is_derived_from_the_prefix
  hf_financial_seed_is_the_checked_pending_state hf_pending_projection_is_derived_without_reading_expected_columns
  hf_source_phase_is_pending

ML \<open>
  if null (Thm_Deps.all_oracles @{thms hf_three_actual_submissions_produce_the_public_call_word
      hf_call_word_uses_the_existing_checked_financial_prefix hf_current_cut_is_derived_from_the_prefix
      hf_financial_seed_is_the_checked_pending_state hf_pending_projection_is_derived_without_reading_expected_columns
      hf_source_phase_is_pending})
  then writeln "HANDOVER_SEED_FRAME_ORACLES_EMPTY"
  else error "Unexpected oracle in the handover seed frame"
\<close>

end
