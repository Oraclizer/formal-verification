theory Recovery_Request_Order_Canary
  imports "Recovery_Boundary_Rollback"
begin

text \<open>This finite-history control distinguishes invocation order from independent selection order,
  and distinguishes equal final states from reply-transcript order. It preserves the imported
  boundary machine and uses no new operational guard.\<close>

fun invoked_requests where
  "invoked_requests [] = []"
| "invoked_requests (Ask c a # events) = (c, a) # invoked_requests events"
| "invoked_requests (e # events) = invoked_requests events"

fun invocation_subsequence where
  "invocation_subsequence [] ys = True"
| "invocation_subsequence (x # xs) [] = False"
| "invocation_subsequence (x # xs) (y # ys) =
     ((x = y \<and> invocation_subsequence xs ys) \<or> invocation_subsequence (x # xs) ys)"

definition prepare_read_select_events where
  "prepare_read_select_events c =
    [Ask c Toy_Spend, Ask c Toy_Look, Flush_Record 0, Publish_Head 0, Select_Head 0, Issue_Reply 0]"

definition prepare_read_select_state where
  "prepare_read_select_state c profile R0 = fold (boundary_step toy_step list_digest profile)
    (prepare_read_select_events c) (genesis_system list_digest profile R0)"

lemma canary_has_collision_free_addresses: "inj list_digest"
  by (rule list_digest_is_injective)

lemma canary_satisfies_the_existing_reply_premise: "replies_follow_effects toy_step"
  by (rule toy_replies_follow_effects)

lemma canary_has_no_rollback:
  "\<forall>e \<in> set (prepare_read_select_events c). \<not> is_witness_rollback e"
  by (simp add: prepare_read_select_events_def)

lemma request_occurrences_keep_the_invocation_order:
  "invoked_requests (prepare_read_select_events c) = [(c, Toy_Spend), (c, Toy_Look)]"
  by (simp add: prepare_read_select_events_def)

lemma the_selected_word_has_the_other_order:
  "ghost_word (prepare_read_select_state c profile R0) = [(c, Toy_Look), (c, Toy_Spend)]"
  by (simp add: prepare_read_select_state_def prepare_read_select_events_def boundary_run_simps list_digest_def)

lemma the_selected_word_is_not_an_invocation_subsequence:
  "\<not> invocation_subsequence (ghost_word (prepare_read_select_state c profile R0))
     (invoked_requests (prepare_read_select_events c))"
  by (simp add: the_selected_word_has_the_other_order request_occurrences_keep_the_invocation_order)

lemma the_observed_replies_are_from_the_selected_word:
  "sys_released (prepare_read_select_state c profile R0) =
     [(0, Toy_Seen (retained_provider R0)), (1, Toy_Token (retained_provider R0))]"
  by (simp add: prepare_read_select_state_def prepare_read_select_events_def boundary_run_simps list_digest_def)

lemma the_endpoint_has_the_committed_effect:
  "sys_endpoint (prepare_read_select_state c profile R0) =
    Some (head_for_record list_digest
      (staged_commit profile (head_for_record list_digest (genesis_record profile R0)) (toy_bump R0)), toy_bump R0)"
  by (simp add: prepare_read_select_state_def prepare_read_select_events_def boundary_run_simps list_digest_def)

lemma state_equivalence_does_not_repair_the_response_order:
  "run_product_action_word toy_step [(c, Toy_Look), (c, Toy_Spend)] R0 =
     run_product_action_word toy_step [(c, Toy_Spend), (c, Toy_Look)] R0"
  "snd (run_word_transcript toy_step [(c, Toy_Look), (c, Toy_Spend)] R0) =
     [Toy_Seen (retained_provider R0), Toy_Token (retained_provider R0)]"
  "snd (run_word_transcript toy_step [(c, Toy_Spend), (c, Toy_Look)] R0) =
     [Toy_Token (retained_provider R0), Toy_Seen (Suc (retained_provider R0))]"
  "snd (run_word_transcript toy_step [(c, Toy_Look), (c, Toy_Spend)] R0) \<noteq>
     snd (run_word_transcript toy_step [(c, Toy_Spend), (c, Toy_Look)] R0)"
  by simp_all

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms canary_has_collision_free_addresses
    canary_satisfies_the_existing_reply_premise canary_has_no_rollback
    request_occurrences_keep_the_invocation_order the_selected_word_has_the_other_order
    the_selected_word_is_not_an_invocation_subsequence the_observed_replies_are_from_the_selected_word
    the_endpoint_has_the_committed_effect state_equivalence_does_not_repair_the_response_order})
  then () else error "Unexpected oracle in request-order feasibility canary"
\<close>

end
