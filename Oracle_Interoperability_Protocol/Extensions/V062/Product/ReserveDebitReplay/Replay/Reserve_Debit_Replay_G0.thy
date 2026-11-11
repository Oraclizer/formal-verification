theory Reserve_Debit_Replay_G0
  imports Wire_Code_Fixture_Replay_Engine
begin

definition rdr_curve_known where
  "rdr_curve_known key message signature \<longleftrightarrow>
    map_of rdr_curve_observations (key,message,signature) \<noteq> None"

definition rdr_event_covered where
  "rdr_event_covered event \<longleftrightarrow>
    rdr_curve_known code_fixture_issuer_key (fixture_token_preimage (fixture_stimulus_token event))
      (fixture_token_signature (fixture_stimulus_token event)) \<and>
    (case fixture_stimulus_packet event of None \<Rightarrow> fixture_stimulus_api event = Code_Fixture_Initialize
     | Some bytes \<Rightarrow> case decode_wire_packet bytes of None \<Rightarrow> False | Some packet \<Rightarrow>
       rdr_curve_known code_fixture_peer_key (envelope_signing_bytes (packet_core packet)) (packet_signature packet))"

definition rdr_hash_domain where
  "rdr_hash_domain \<longleftrightarrow> distinct (map fst code_fixture_hash_facts) \<and>
    list_all (\<lambda>raw. map_of code_fixture_hash_facts (code_session_grants_domain @ raw) \<noteq> None)
      [code_fixture_grants_json_0,code_fixture_grants_json_1]"

definition rdr_trace_domain where
  "rdr_trace_domain events \<longleftrightarrow>
    distinct (map fst rdr_curve_observations) \<and> rdr_hash_domain \<and> list_all rdr_event_covered events"

definition rdr_checked_run where
  "rdr_checked_run events =
    (if rdr_trace_domain events then Some (code_fixture_run_stimuli events code_fixture_replay_initial) else None)"

text \<open>
  The finite input domain consumes exact primitive lookups. A missing or
  duplicate table entry returns metadata None. A recorded False value belongs
  to the corresponding primitive observation. The result is computed by the original
  replay program; no output theorem, source outcome or after-state is an input.
\<close>

lemma rdr_uncovered_inputs_produce_no_protocol_result:
  "\<not> rdr_trace_domain events \<Longrightarrow> rdr_checked_run events = None"
  by (simp add: rdr_checked_run_def)

lemma rdr_checked_run_is_the_original_stateful_program:
  "rdr_trace_domain events \<Longrightarrow>
    rdr_checked_run events = Some (code_fixture_run_stimuli events code_fixture_replay_initial)"
  by (simp add: rdr_checked_run_def)

lemma rdr_replay_counts_seeds_separately:
  "length code_fixture_stimuli = 15"
  "length (filter (\<lambda>event. fixture_stimulus_api event = Code_Fixture_Initialize) code_fixture_stimuli) = 2"
  "length rdr_same_cut_stimuli = 3"
  "length (filter (\<lambda>event. fixture_stimulus_api event = Code_Fixture_Initialize) rdr_same_cut_stimuli) = 1"
  by (simp_all add: code_fixture_stimuli_def rdr_same_cut_stimuli_def)

lemma rdr_admission_refusal_preserves_every_projected_component:
  assumes api: "fixture_stimulus_api event \<noteq> Code_Fixture_Initialize"
    and packet: "fixture_stimulus_packet event = Some bytes"
    and refused: "code_fixture_packet_admission
      (fixture_stimulus_api event \<in> {Code_Fixture_Resolve,Code_Fixture_Resolve_Response})
      (fixture_stimulus_clock event) bytes = Some reason"
  shows "code_fixture_replay_step event state =
    (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation reason))"
  using assms by (simp add: code_fixture_replay_step_def Let_def)

lemma rdr_exact_retained_call_reuses_its_result_without_another_effect:
  assumes active: "code_source_active_identity (code_fixture_authenticate_session now) token
      \<lparr>proof_session = native_session (finite_selected_native chosen),proof_epoch = 9\<rparr>
      (code_fixture_current_identity_snapshot (replay_financial_slice state)) = Some identity"
    and caller: "identity_principal identity = wire_principal (finite_selected_core chosen)"
      "identity_domain identity = wire_source_domain (finite_selected_core chosen)"
    and binding: "map_of (replay_transport state) (authenticated_wire_message_id (finite_selected_core chosen)) =
      Some (encode_wire_core (finite_selected_core chosen))"
    and execute: "code_fixture_authorize bytes chosen token now Execute_Ordinary (replay_financial_slice state) \<noteq> None"
    and retained: "map_of (replay_calls state) (native_id (finite_selected_native chosen)) =
      Some (finite_selected_payload chosen,outcome)"
    and receipt: "code_fixture_authorize bytes chosen token now Read_Receipt (replay_financial_slice state) \<noteq> None"
  shows "code_fixture_receive_selected bytes chosen token now state =
    (state,Code_Fixture_Replay_Received Code_Identical outcome)"
  using assms by (simp add: code_fixture_receive_selected_def code_compare_binding_def Let_def)

lemma rdr_program_preserves_the_number_of_input_occurrences:
  "length (code_fixture_run_stimuli events state) = length events"
  by (induction events arbitrary: state) (simp_all add: Let_def)

lemma rdr_checked_trace_has_one_model_row_per_input_occurrence:
  assumes "rdr_checked_run events = Some rows"
  shows "length rows = length events"
proof -
  have rows_eq: "rows = code_fixture_run_stimuli events code_fixture_replay_initial"
    using assms by (auto simp: rdr_checked_run_def split: if_splits)
  show ?thesis by (simp only: rows_eq rdr_program_preserves_the_number_of_input_occurrences)
qed

definition rdr_fixed_domain_observations where
  "rdr_fixed_domain_observations = (rdr_trace_domain code_fixture_stimuli,rdr_trace_domain rdr_same_cut_stimuli)"

definition rdr_fixed_token_observations where
  "rdr_fixed_token_observations =
    (code_fixture_authenticate_session 105 code_fixture_token_0 \<lparr>proof_session = 2,proof_epoch = 9\<rparr>,
     code_fixture_authenticate_session 106 code_fixture_token_1 \<lparr>proof_session = 2,proof_epoch = 9\<rparr>)"

text \<open>
  Generic step, retained-binding, metadata and occurrence contracts are
  kernel checked here. The two fixed primitive-domain values and exact-token
  observations are computed by the generated standalone model. They are not
  concrete kernel-normalization theorems. No expected truth value is an input.
  The guard remains executable before every checked trace. Standalone results
  are finite execution evidence with code-generation/runtime and crypto TCBs.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      rdr_uncovered_inputs_produce_no_protocol_result
      rdr_checked_run_is_the_original_stateful_program
      rdr_replay_counts_seeds_separately
      rdr_admission_refusal_preserves_every_projected_component
      rdr_exact_retained_call_reuses_its_result_without_another_effect
      rdr_program_preserves_the_number_of_input_occurrences
      rdr_checked_trace_has_one_model_row_per_input_occurrence})
  then () else error "Unexpected oracle in the independent replay composition"
\<close>

end
