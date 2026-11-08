theory Exact_Source_Trace
  imports Exactly_Once
begin

definition outcome_calls where
  "outcome_calls s = product_calls (outcome_source s)"

definition exact_calls where
  "exact_calls s = outcome_calls (origin_outcomes (settlement_primary s))"

context source_attestation
begin

lemma submitted_call_source_is_stutter_or_lock_step:
  "let next = submit_authoritative_call permitted verified maintainers registered entry who call_id payload s
    in outcome_source next = outcome_source s \<or>
       outcome_source next = lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered
          (Lock_Submit entry who call_id (payload_envelope payload) (payload_credential payload)) (outcome_source s)"
  by (simp add: Let_def submit_authoritative_call_def submit_new_authoritative_call_def store_product_result_def
      split: if_splits option.splits prod.splits)

lemma submitted_call_has_a_public_segment:
  "\<exists>word. outcome_calls (submit_authoritative_call permitted verified maintainers registered entry who call_id payload s) =
      finality_calls.run_calls word (outcome_calls s)"
proof -
  let ?step = "lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered
    (Lock_Submit entry who call_id (payload_envelope payload) (payload_credential payload)) (outcome_source s)"
  have lift: "\<exists>word. product_calls ?step = finality_calls.run_calls word (outcome_calls s)"
    unfolding outcome_calls_def by (rule lock_product_step_is_public_segment)
  let ?next = "submit_authoritative_call permitted verified maintainers registered entry who call_id payload s"
  have "outcome_source ?next = outcome_source s \<or> outcome_source ?next = ?step"
    using submitted_call_source_is_stutter_or_lock_step[of permitted verified maintainers registered entry who call_id payload s]
    by (simp only: Let_def)
  then show ?thesis
  proof
    assume "outcome_source ?next = outcome_source s"
    then show ?thesis by (intro exI[of _ "[]"]) (simp add: outcome_calls_def)
  next
    assume "outcome_source ?next = ?step"
    then show ?thesis using lift by (simp add: outcome_calls_def)
  qed
qed

lemma origin_call_has_a_public_segment:
  "\<exists>word. outcome_calls (origin_outcomes (submit_origin_call permitted verified maintainers registered entry who call_id payload s)) =
      finality_calls.run_calls word (outcome_calls (origin_outcomes s))"
proof -
  let ?perm = "\<lambda>route actor command. permitted route actor command \<and>
    origin_command_allowed s (payload_envelope payload) (payload_origin_epoch payload) command"
  let ?next = "submit_authoritative_call ?perm verified maintainers registered entry who call_id payload (origin_outcomes s)"
  have origin_cases: "origin_outcomes (submit_origin_call permitted verified maintainers registered entry who call_id payload s) =
    origin_outcomes s \<or> origin_outcomes (submit_origin_call permitted verified maintainers registered entry who call_id payload s) = ?next"
    by (simp add: submit_origin_call_def Let_def origin_metadata_retention_keeps_the_authority_result
        split: if_splits option.splits prod.splits)
  have lift: "\<exists>word. outcome_calls ?next = finality_calls.run_calls word (outcome_calls (origin_outcomes s))"
    by (rule submitted_call_has_a_public_segment)
  from origin_cases show ?thesis
  proof
    assume "origin_outcomes (submit_origin_call permitted verified maintainers registered entry who call_id payload s) = origin_outcomes s"
    then show ?thesis by (intro exI[of _ "[]"]) simp
  next
    assume "origin_outcomes (submit_origin_call permitted verified maintainers registered entry who call_id payload s) = ?next"
    then show ?thesis using lift by simp
  qed
qed

lemma completing_a_result_preserves_source_calls:
  "outcome_calls (fst (complete_authoritative_result verified who call_id payload s)) = outcome_calls s"
  by (simp add: outcome_calls_def complete_authoritative_result_def split: option.splits if_splits)

lemma lock_environment_step_has_a_public_segment:
  "\<exists>word. exact_calls (apply_non_submit_lock_action permitted maintainers registered action s) =
    finality_calls.run_calls word (exact_calls s)"
  unfolding apply_non_submit_lock_action_def update_settlement_outcomes_def exact_calls_def outcome_calls_def Let_def
  by (simp add: lock_product_step_is_public_segment)

lemma source_restart_has_a_public_segment:
  "\<exists>word. outcome_calls (recover_outcome_world candidate s) = finality_calls.run_calls word (outcome_calls s)"
proof (cases "candidate = Some (authoritative_outcome_snapshot s) \<and>
    call_local_status (outcome_calls s) = Endpoint_Down \<and> call_connection (outcome_calls s) = Authority_Connected")
  case True
  then show ?thesis by (intro exI[of _ "[Recover_Local_Endpoint]"])
    (simp add: outcome_calls_def recover_outcome_world_def product_restart_def product_apply_public_def)
next
  case False
  then show ?thesis by (intro exI[of _ "[]"])
    (auto simp: outcome_calls_def recover_outcome_world_def product_restart_def split: if_splits)
qed

lemma exact_step_has_a_public_segment:
  "\<exists>word. exact_calls (exact_step permitted verified maintainers registered verified_ack action s) =
    finality_calls.run_calls word (exact_calls s)"
proof (cases action)
  case (Exact_Submit entry who call_id payload)
  then show ?thesis by (simp add: exact_calls_def origin_call_has_a_public_segment)
next
  case (Exact_Install who epoch changes sessions)
  then show ?thesis by (simp add: lock_environment_step_has_a_public_segment)
next
  case (Exact_Link connection)
  then show ?thesis by (simp add: lock_environment_step_has_a_public_segment)
next
  case Exact_Crash
  then show ?thesis by (intro exI[of _ "[Crash_Local_Endpoint]"])
    (simp add: exact_calls_def outcome_calls_def update_settlement_outcomes_def crash_outcome_world_def
      product_crash_def product_apply_public_def)
next
  case (Exact_Recover candidate)
  have recovery: "\<exists>word. outcome_calls (recover_outcome_world (Some (authoritative_outcome_snapshot
       (origin_outcomes (settlement_primary s)))) (origin_outcomes (settlement_primary s))) =
    finality_calls.run_calls word (exact_calls s)"
    unfolding exact_calls_def by (rule source_restart_has_a_public_segment)
  show ?thesis
  proof (cases candidate)
    case None
    with Exact_Recover show ?thesis by (intro exI[of _ "[]"]) simp
  next
    case (Some candidate_state)
    show ?thesis
    proof (cases "settlement_snapshot candidate_state = settlement_snapshot s")
      case True
      with Some Exact_Recover recovery show ?thesis
        by (simp add: exact_calls_def update_settlement_outcomes_def Let_def)
    next
      case False
      with Some Exact_Recover show ?thesis by (intro exI[of _ "[]"]) simp
    qed
  qed
qed (intro exI[of _ "[]"], simp add: exact_calls_def update_settlement_outcomes_def
    completing_a_result_preserves_source_calls secondary_steps_preserve_primary)+

lemma exact_product_trace_is_a_public_word:
  "\<exists>word. exact_calls (run_exact_product permitted verified maintainers registered verified_ack actions s) =
    finality_calls.run_calls word (exact_calls s)"
proof (induction actions arbitrary: s)
  case Nil
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons action actions)
  let ?step = "exact_step permitted verified maintainers registered verified_ack action s"
  obtain first where first: "exact_calls ?step = finality_calls.run_calls first (exact_calls s)"
    using exact_step_has_a_public_segment by blast
  obtain rest where rest: "exact_calls (run_exact_product permitted verified maintainers registered verified_ack actions ?step) =
    finality_calls.run_calls rest (exact_calls ?step)" using Cons.IH by blast
  show ?case by (intro exI[of _ "first @ rest"]) (simp add: first rest lock_public_segments_append)
qed

end

end
