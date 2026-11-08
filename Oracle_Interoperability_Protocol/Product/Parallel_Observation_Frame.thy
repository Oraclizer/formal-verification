theory Parallel_Observation_Frame
  imports Queue_Action_Locality
begin

definition service_settlement where
  "service_settlement s = read_authority (regulated_read_world s)"

definition replace_service_jobs where
  "replace_service_jobs jobs s =
    (let reads = regulated_read_world s; authority = read_authority reads
     in replace_regulated_reads (reads\<lparr>read_authority := authority\<lparr>settlement_jobs := jobs\<rparr>\<rparr>) s)"

lemma replace_service_jobs_reads [simp]:
  "regulated_read_world (replace_service_jobs jobs s) =
    (regulated_read_world s)\<lparr>read_authority := (service_settlement s)\<lparr>settlement_jobs := jobs\<rparr>\<rparr>"
  by (simp add: replace_service_jobs_def service_settlement_def regulated_read_world_def replace_regulated_reads_def Let_def)

lemma replace_service_jobs_exact_state [simp]:
  "service_settlement (replace_service_jobs jobs s) = (service_settlement s)\<lparr>settlement_jobs := jobs\<rparr>"
  by (simp add: service_settlement_def)

lemma replace_service_jobs_same [simp]:
  "replace_service_jobs (settlement_jobs (service_settlement s)) s = s"
  by (simp add: replace_service_jobs_def service_settlement_def regulated_read_world_def replace_regulated_reads_def Let_def)

lemma replace_service_jobs_twice [simp]:
  "replace_service_jobs b (replace_service_jobs a s) = replace_service_jobs b s"
  by (simp add: replace_service_jobs_def service_settlement_def regulated_read_world_def replace_regulated_reads_def Let_def)

lemma replace_service_jobs_same_source [simp]:
  "identity_source (replace_service_jobs jobs s) = identity_source s"
  by (simp add: identity_source_def service_settlement_def observed_product_source_def)

lemma replace_service_jobs_same_receipts [simp]:
  "current_product_outcomes (replace_service_jobs jobs s) = current_product_outcomes s"
  "legal_receipts (regulated_orders (replace_service_jobs jobs s)) = legal_receipts (regulated_orders s)"
  "spend_receipts (replace_service_jobs jobs s) = spend_receipts s"
  by (simp_all add: current_product_outcomes_def legal_underlying_outcomes_def replace_service_jobs_def
      replace_regulated_reads_def regulated_read_world_def Let_def)

lemma queue_update_does_not_change_the_authority_queries [simp]:
  "observed_product_source (s\<lparr>settlement_jobs := jobs\<rparr>) = observed_product_source s"
  "observed_product_cut (s\<lparr>settlement_jobs := jobs\<rparr>) = observed_product_cut s"
  "exact_calls (s\<lparr>settlement_jobs := jobs\<rparr>) = exact_calls s"
  "authoritative_read_core (s\<lparr>settlement_jobs := jobs\<rparr>) = authoritative_read_core s"
  by (simp_all add: observed_product_source_def observed_product_cut_def exact_calls_def authoritative_read_core_def)

lemma queue_update_does_not_change_availability [simp]:
  "read_authority_available (r\<lparr>read_authority := (read_authority r)\<lparr>settlement_jobs := jobs\<rparr>\<rparr>) =
    read_authority_available r"
  by (simp add: read_authority_available_def)

lemma queue_update_does_not_change_asset_registration [simp]:
  "read_asset_registered query (r\<lparr>read_authority := (read_authority r)\<lparr>settlement_jobs := jobs\<rparr>\<rparr>) =
    read_asset_registered query r"
  by (cases "registration_sensitive_asset query") (simp_all add: read_asset_registered_def)

lemma replacing_queue_keeps_the_retained_primary_fields:
  "capture_retained_product (replace_service_jobs jobs s) = (capture_retained_product s)\<lparr>retained_secondary := jobs\<rparr>"
  by (simp add: capture_retained_product_def replace_service_jobs_def replace_regulated_reads_def regulated_read_world_def Let_def)

context source_attestation
begin

lemma queue_update_does_not_change_exact_prefixes [simp]:
  "authority_prefix_snapshot revision (s\<lparr>settlement_jobs := jobs\<rparr>) = authority_prefix_snapshot revision s"
  by (simp add: authority_prefix_snapshot_def authority_prefix_core_def)

lemma individual_authorized_read_ignores_the_queue:
  "authorized_read_value identity proof target request
     (reads\<lparr>read_authority := (read_authority reads)\<lparr>settlement_jobs := jobs\<rparr>\<rparr>) =
   authorized_read_value identity proof target request reads"
  by (cases request) (simp_all add: read_current_product_def read_historical_product_def read_access_bound_def
      cache_is_current_for_def Let_def split: option.splits if_splits)

lemma signed_endpoint_read_ignores_the_queue:
  "read_at_identity_endpoint directory policy authenticate verify_read token proof target request (replace_service_jobs jobs s) =
   read_at_identity_endpoint directory policy authenticate verify_read token proof target request s"
  by (simp add: read_at_identity_endpoint_def service_settlement_def individual_authorized_read_ignores_the_queue Let_def
      split: option.splits)

lemma discarding_the_process_cache_commutes_with_queue_replacement:
  "discard_process_cache (replace_service_jobs jobs s) = replace_service_jobs jobs (discard_process_cache s)"
  by (simp add: discard_process_cache_def replace_service_jobs_def service_settlement_def regulated_read_world_def
      replace_regulated_reads_def Let_def)

lemma retained_current_or_historical_reply_ignores_the_queue:
  "read_with_revalidated_cache directory policy authenticate verify_read token proof target request supplied
    (replace_service_jobs jobs s) =
   read_with_revalidated_cache directory policy authenticate verify_read token proof target request supplied s"
  unfolding read_with_revalidated_cache_def Let_def
  by (simp add: discarding_the_process_cache_commutes_with_queue_replacement signed_endpoint_read_ignores_the_queue
      valid_recovered_cache_def cache_is_current_for_def service_settlement_def
      split: prod.splits identity_read_request.splits identity_read_reply.splits product_read_reply.splits option.splits)

lemma query_cache_capture_is_independent_of_settlement_jobs:
  "query_cache (capture_product_cache permitted who session query
       (reads\<lparr>read_authority := (read_authority reads)\<lparr>settlement_jobs := jobs\<rparr>\<rparr>)) =
   query_cache (capture_product_cache permitted who session query reads)"
  by (simp add: capture_product_cache_def read_access_bound_def Let_def split: option.splits if_splits)

lemma capturing_the_observation_does_not_read_the_queue:
  "capture_revalidated_cache directory policy authenticate verify_read token proof target query (replace_service_jobs jobs s) =
   capture_revalidated_cache directory policy authenticate verify_read token proof target query s"
  unfolding capture_revalidated_cache_def discarding_the_process_cache_commutes_with_queue_replacement
  by (simp add: capture_at_identity_endpoint_def service_settlement_def regulated_read_world_def
      replace_regulated_reads_def query_cache_capture_is_independent_of_settlement_jobs Let_def
      identity_source_def replace_service_jobs_def split: option.splits if_splits)

lemma exact_endpoint_receipt_ignores_settlement_jobs:
  "exact_endpoint_receipt verified actor action (replace_service_jobs jobs s) =
   exact_endpoint_receipt verified actor action s"
proof -
  have outcomes: "legal_underlying_outcomes (governed_legal (regulated_orders (replace_service_jobs jobs s))) =
    legal_underlying_outcomes (governed_legal (regulated_orders s))"
    using replace_service_jobs_same_receipts(1)[of jobs s] by (simp only: current_product_outcomes_def)
  show ?thesis
    by (induction verified actor action s rule: exact_endpoint_receipt.induct)
      (simp_all add: outcomes current_product_outcomes_def[symmetric])
qed

lemma authorized_receipt_observation_ignores_the_queue:
  "read_authorized_receipt directory policy authenticate verify verified route token proof target action (replace_service_jobs jobs s) =
   read_authorized_receipt directory policy authenticate verify verified route token proof target action s"
proof -
  have access: "authorized_endpoint_action directory policy authenticate verify route token proof target action (replace_service_jobs jobs s) =
    authorized_endpoint_action directory policy authenticate verify route token proof target action s"
    unfolding authorized_endpoint_action_def
    by (cases "external_call_claim action") (simp_all split: prod.splits)
  show ?thesis
  proof (cases "external_call_claim action")
    case None
    then show ?thesis by (simp add: read_authorized_receipt_def)
  next
    case (Some item)
    obtain operation actor call_id payload where item: "item = (operation, actor, call_id, payload)"
      by (metis prod.exhaust)
    show ?thesis using Some item
      by (cases operation) (simp_all add: read_authorized_receipt_def access exact_endpoint_receipt_ignores_settlement_jobs)
  qed
qed

end

end
