theory Promotion_Endpoint
  imports Recovered_Observations
begin

context source_attestation
begin

lemma durable_execution_uses_the_same_final_gate_on_every_route:
  "durable_execute directory policy authenticate verify endorse first token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
   durable_execute directory policy authenticate verify endorse second token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s"
  unfolding durable_execute_def authorized_endpoint_action_def endpoint_call_allowed_on_def by (rule refl)

lemma an_execution_reply_comes_from_the_authenticated_caller_partition:
  assumes reply: "snd (durable_execute directory policy authenticate verify endorse route token proof target action authorization
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s) =
     Durable_Execution_Reply result"
  obtains operation actor call_id payload identity where "external_call_claim action = Some (operation, actor, call_id, payload)"
    "authenticate token = Some identity"
    "identity_principal identity = fst call_id" "envelope_caller (payload_envelope payload) = fst call_id"
    "verify identity proof target operation call_id payload"
proof -
  have admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target action s"
  proof (rule ccontr)
    assume denied: "\<not> authorized_endpoint_action directory policy authenticate verify route token proof target action s"
    have "durable_execute directory policy authenticate verify endorse route token proof target action authorization
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s =
      (s, Durable_Execution_Reject)"
    proof (cases "external_call_claim action")
      case None
      then show ?thesis by (simp add: durable_execute_def)
    next
      case (Some claimed)
      obtain operation actor call_id payload where claimed: "claimed = (operation, actor, call_id, payload)"
        by (cases claimed) auto
      from Some claimed denied show ?thesis
        by (cases "execution_receipt_request action") (simp_all add: durable_execute_def)
    qed
    with reply show False by simp
  qed
  show thesis
  proof (rule accepted_endpoint_uses_a_submitted_authenticated_namespace[OF admitted])
    fix operation actor call_id payload identity
    assume claim: "external_call_claim action = Some (operation, actor, call_id, payload)"
      and token: "authenticate token = Some identity"
      and "directory (fst call_id) = Some identity"
      and principal: "identity_principal identity = fst call_id"
      and envelope: "envelope_caller (payload_envelope payload) = fst call_id"
      and verified: "verify identity proof target operation call_id payload"
    show thesis by (rule that[OF claim token principal envelope verified])
  qed
qed

lemma an_unbound_checked_cut_does_not_authorize_a_new_source_effect:
  assumes "expected \<noteq> current_product_cut (identity_source s)"
  shows "outcome_source (current_product_outcomes (run_fresh_durable_effect permitted verified maintainers registered verified_ack
      legal_grant order_verified spend_grant spend_verified read_permitted
      (Ordinary_Product_Action (Execute_Checked entry actor expected call_id payload)) s)) =
    outcome_source (current_product_outcomes s)"
proof (cases "governed_command (envelope_command (payload_envelope payload)) \<or>
      expected \<noteq> envelope_cut (payload_envelope payload)")
  case True
  then show ?thesis by (simp add: Let_def)
next
  case False
  with assms show ?thesis
    by (cases "call_connection (product_calls (identity_source s)) = Authority_Connected")
      (simp_all add: Let_def checked_refusal_keeps_the_exact_underlying_source)
qed

lemma cleared_current_reply_has_the_exact_actual_value:
  assumes "query_cache reads query = None"
    "read_current_product permitted who session query expected reads = Current_Cut_Value observed result"
  shows "observed = observed_product_cut (read_authority reads) \<and>
    result = stored_query query (capture_snapshot (authoritative_read_core (read_authority reads)))"
  using assms by (auto simp: read_current_product_def Let_def split: if_splits)

lemma discard_cache_keeps_the_read_authority [simp]:
  "read_authority (regulated_read_world (discard_process_cache s)) = read_authority (regulated_read_world s)"
  "query_cache (regulated_read_world (discard_process_cache s)) = (\<lambda>_. None)"
  by (simp_all add: discard_process_cache_def regulated_read_world_def replace_regulated_reads_def)

theorem a_current_reply_from_the_actual_wire_ready_endpoint_has_its_exact_cut:
  assumes response: "read_with_revalidated_cache directory policy authenticate verify_read token proof target
     (Current_Data query expected) supplied s = Authorized_Data (Current_Cut_Value observed result)"
  shows "observed = observed_product_cut (read_authority (regulated_read_world s)) \<and>
    result = stored_query query (capture_snapshot (authoritative_read_core (read_authority (regulated_read_world s))))"
proof -
  let ?request = "Current_Data query expected"
  let ?base = "read_at_identity_endpoint directory policy authenticate verify_read token proof target ?request (discard_process_cache s)"
  have direct: "?base = Authorized_Data (Current_Cut_Value observed result)"
  proof (cases "?base")
    case (Authorized_Data trusted)
    from Authorized_Data response show ?thesis
      by (cases trusted; cases supplied)
        (simp_all add: read_with_revalidated_cache_def Let_def split: if_splits)
  qed (use response in \<open>simp_all add: read_with_revalidated_cache_def Let_def\<close>)
  obtain identity where source: "authenticate token = Some identity"
    and reply: "read_current_product (\<lambda>_ _ _. True) (identity_principal identity) (proof_session proof)
      query expected (regulated_read_world (discard_process_cache s)) = Current_Cut_Value observed result"
    using direct by (cases "authenticate token")
      (auto simp: read_at_identity_endpoint_def Let_def split: if_splits)
  show ?thesis
    using cleared_current_reply_has_the_exact_actual_value[OF _ reply] by simp
qed

end

end
