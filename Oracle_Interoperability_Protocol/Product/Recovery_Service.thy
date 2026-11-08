theory Recovery_Service
  imports Recovered_Source_Obligations
begin

datatype 'token retained_service_action =
    Service_Execute identity_route 'token session_proof nat regulated_product_action "'token recovery_endorsement option"
  | Service_Receipt identity_route 'token session_proof nat regulated_product_action
  | Service_Read 'token session_proof nat identity_read_request "product_cache_entry option"
  | Service_Capture 'token session_proof nat application_query
  | Service_Handover 'token 'token product_principal ownership_transfer
  | Service_Maintenance exact_action
  | Service_Source_Probe source_key "source_certificate option"

datatype retained_service_reply =
    Service_Execution_Result durable_execution_reply
  | Service_Receipt_Result "authorized_receipt option"
  | Service_Read_Result identity_read_reply
  | Service_Cache_Result "product_cache_entry option"
  | Service_Handover_Result bool
  | Service_Maintenance_Result bool
  | Service_Secondary_Result "product_secondary_job option"
  | Service_Source_Result restart_source_action

fun persistent_maintenance_allowed where
  "persistent_maintenance_allowed (Exact_Submit entry who call_id payload) = False"
| "persistent_maintenance_allowed (Exact_Collect who call_id payload) = False"
| "persistent_maintenance_allowed Exact_Crash = False"
| "persistent_maintenance_allowed (Exact_Recover candidate) = False"
| "persistent_maintenance_allowed action = True"

fun persistent_maintenance_reply where
  "persistent_maintenance_reply (Exact_Dispatch_Secondary key) before after =
    Service_Secondary_Result (settlement_jobs (read_authority (regulated_read_world after)) key)"
| "persistent_maintenance_reply action before after = Service_Maintenance_Result (after \<noteq> before)"

context source_attestation
begin

fun live_product_service_step where
  "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Service_Execute route token proof target action endorsement) s =
    (let result = durable_execute directory policy authenticate verify endorse route token proof target action endorsement
       legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack s
     in (fst result, Service_Execution_Result (snd result)))"
| "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Service_Receipt route token proof target action) s =
    (s, Service_Receipt_Result (read_authorized_receipt directory policy authenticate verify verified route token proof target action s))"
| "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Service_Read token proof target request supplied) s =
    (s, Service_Read_Result (read_with_revalidated_cache directory read_policy authenticate verify_read token proof target request supplied s))"
| "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Service_Capture token proof target query) s =
    (s, Service_Cache_Result (capture_revalidated_cache directory read_policy authenticate verify_read token proof target query s))"
| "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Service_Handover owner_token successor_token maintainer proposal) s =
    (let updated = handover_product_owner directory policy authenticate approve owner_token successor_token maintainer
         maintainers registered proposal s in (updated, Service_Handover_Result (updated \<noteq> s)))"
| "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Service_Maintenance action) s =
    (if persistent_maintenance_allowed action then let reads = regulated_read_world s;
       updated = replace_regulated_reads (reads\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
         action (read_authority reads)\<rparr>) s
      in (updated, persistent_maintenance_reply action s updated)
     else (s, Service_Maintenance_Result False))"
| "live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    (Service_Source_Probe key evidence) s =
    (s, Service_Source_Result (next_recovery_source_action key evidence (identity_source s)))"

definition serve_durable_projection where
  "serve_durable_projection directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    connection action s =
    (let result = live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
       legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
       action (reopen_retained_product connection (capture_retained_product s))
     in (fst result, snd result))"

end

end
