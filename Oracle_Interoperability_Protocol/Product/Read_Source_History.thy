theory Read_Source_History
  imports Reads_Cache
begin

context source_attestation
begin

lemma authoritative_dispatch_only_appends_results:
  "\<exists>suffix. call_authority_log (finality_calls.dispatch_client_call call_id command m) = call_authority_log m @ suffix"
proof (cases "call_local_status m = Endpoint_Up \<and> call_connection m = Authority_Connected \<and>
      map_option fst (call_invocations m call_id) = Some command")
  case False
  have waiting: "finality_calls.dispatch_client_call call_id command m = m\<lparr>call_history := call_history m @ [Call_Waiting call_id]\<rparr>"
    by (simp only: finality_calls.dispatch_client_call_def False if_False)
  show ?thesis by (intro exI[of _ "[]"]) (simp add: waiting)
next
  case True
  note ready = this
  show ?thesis
  proof (cases "call_authority_results m call_id")
    case None
    let ?reply = "snd (execute_finality_client command (call_authority_state m))"
    show ?thesis using ready None
      by (intro exI[of _ "[Authority_Executed call_id command ?reply]"])
        (simp add: finality_calls.dispatch_client_call_def finality_calls.execute_authority_once_def Let_def)
  next
    case (Some stored)
    show ?thesis using ready Some
      by (intro exI[of _ "[]"])
        (simp add: finality_calls.dispatch_client_call_def finality_calls.execute_authority_once_def
          split: prod.splits if_splits)
  qed
qed

lemma public_step_only_appends_authority_log:
  fixes action :: product_public_action
  shows "\<exists>suffix. call_authority_log (finality_calls.call_step action m) = call_authority_log m @ suffix"
proof (cases action)
  case (Dispatch_Call call_id command)
  then show ?thesis by (simp add: authoritative_dispatch_only_appends_results)
next
  case (Apply_Authority_Input input)
  let ?reply = "snd (execute_finality_environment input (call_authority_state m))"
  show ?thesis using Apply_Authority_Input by (intro exI[of _ "[Authority_Input input ?reply]"])
    (simp add: finality_calls.apply_authority_input_def Let_def)
qed (intro exI[of _ "[]"], simp add: finality_calls.begin_client_call_def finality_calls.collect_client_response_def
    finality_calls.complete_client_call_def split: option.splits prod.splits if_splits)+

lemma public_word_only_appends_authority_log:
  fixes word :: "product_public_action list"
  shows "\<exists>suffix. call_authority_log (finality_calls.run_calls word m) = call_authority_log m @ suffix"
proof (induction word arbitrary: m)
  case Nil
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons action word)
  let ?next = "finality_calls.call_step action m"
  obtain first where first: "call_authority_log ?next = call_authority_log m @ first"
    using public_step_only_appends_authority_log[of action m] by blast
  obtain later where later: "call_authority_log (finality_calls.run_calls word ?next) = call_authority_log ?next @ later"
    using Cons.IH[of ?next] by blast
  show ?case by (intro exI[of _ "first @ later"]) (simp add: first later)
qed

lemma exact_authority_step_keeps_every_historical_prefix:
  fixes permitted verified maintainers registered verified_ack action
  assumes "revision \<le> cut_revision (observed_product_cut s)"
  defines "next \<equiv> exact_step permitted verified maintainers registered verified_ack action s"
  shows "authority_prefix_snapshot revision next = authority_prefix_snapshot revision s"
proof -
  obtain word where calls: "exact_calls next = finality_calls.run_calls word (exact_calls s)"
    using exact_step_has_a_public_segment[of permitted verified maintainers registered verified_ack action s]
    unfolding next_def by blast
  obtain suffix where longer: "call_authority_log (exact_calls next) = call_authority_log (exact_calls s) @ suffix"
    using public_word_only_appends_authority_log[of word "exact_calls s"] unfolding calls by blast
  have genesis: "call_genesis (exact_calls next) = call_genesis (exact_calls s)"
    by (simp add: calls)
  have bound: "revision \<le> length (call_authority_log (exact_calls s))"
    using assms(1) by (simp add: observed_revision_is_the_public_log_length)
  show ?thesis using bound
    by (simp add: authority_prefix_snapshot_def authority_prefix_core_def observed_revision_is_the_public_log_length
        longer genesis take_append)
qed

definition authenticated_cache_invariant where
  "authenticated_cache_invariant s \<longleftrightarrow> (\<forall>query entry. query_cache s query = Some entry \<longrightarrow> cache_has_source_value s entry)"

lemma initial_read_cache_is_authentic:
  "authenticated_cache_invariant (initial_product_reads provider authority)"
  by (simp add: authenticated_cache_invariant_def initial_product_reads_def)

lemma cache_capture_preserves_source_values:
  assumes "authenticated_cache_invariant s"
  shows "authenticated_cache_invariant (capture_product_cache permitted who session query s)"
  using assms by (auto simp: authenticated_cache_invariant_def capture_product_cache_def cache_has_source_value_def Let_def
      split: option.splits if_splits)

lemma authority_advance_preserves_cached_historical_values:
  fixes permitted verified maintainers registered verified_ack action
  assumes inv: "authenticated_cache_invariant s"
  defines "next \<equiv> exact_step permitted verified maintainers registered verified_ack action (read_authority s)"
  shows "authenticated_cache_invariant (s\<lparr>read_authority := next\<rparr>)"
proof (unfold authenticated_cache_invariant_def, intro allI impI)
  fix query entry
  assume "query_cache (s\<lparr>read_authority := next\<rparr>) query = Some entry"
  then have old: "cache_has_source_value s entry" using inv
    by (auto simp: authenticated_cache_invariant_def)
  then obtain snapshot where at: "authority_prefix_snapshot (cut_revision (cached_cut entry)) (read_authority s) = Some snapshot"
    and cached_eq: "cached_value entry = stored_query (cached_query entry) snapshot"
    unfolding cache_has_source_value_def by blast
  have bound: "cut_revision (cached_cut entry) \<le> cut_revision (observed_product_cut (read_authority s))"
    unfolding observed_revision_is_the_public_log_length
    by (rule conjunct1[OF authority_prefix_snapshot_has_exact_requested_history[OF at]])
  have same: "authority_prefix_snapshot (cut_revision (cached_cut entry)) next = Some snapshot"
    using exact_authority_step_keeps_every_historical_prefix[OF bound, where permitted=permitted and verified=verified
      and maintainers=maintainers and registered=registered and verified_ack=verified_ack and action=action] at
    by (simp add: next_def)
  show "cache_has_source_value (s\<lparr>read_authority := next\<rparr>) entry"
    using same cached_eq by (auto simp: cache_has_source_value_def)
qed

end

end
