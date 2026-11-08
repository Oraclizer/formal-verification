theory Parallel_Service
  imports Parallel_Observation_Frame
begin

datatype service_dependency =
    Shared_Authority
  | Authoritative_Revision
  | Exact_Completion_History
  | Authoritative_Read_Provider
  | Primary_Publication_Dependency source_key
  | Exact_Settlement_Slot settlement_identity

datatype service_schedule_class =
    Service_Observation
  | Service_Slot resolved_settlement_action
  | Service_Serial

fun classify_service_action where
  "classify_service_action (Service_Receipt route token proof target action) s = Service_Observation"
| "classify_service_action (Service_Read token proof target request supplied) s = Service_Observation"
| "classify_service_action (Service_Capture token proof target query) s = Service_Observation"
| "classify_service_action (Service_Source_Probe key evidence) s = Service_Observation"
| "classify_service_action (Service_Maintenance action) s =
    (if is_settlement_action action then case queue_action_at action s of None \<Rightarrow> Service_Observation
     | Some resolved \<Rightarrow> Service_Slot resolved else Service_Serial)"
| "classify_service_action action s = Service_Serial"

definition service_access_footprint where
  "service_access_footprint action s =
    (case classify_service_action action s of
       Service_Observation \<Rightarrow> ({Shared_Authority, Authoritative_Revision, Exact_Completion_History, Authoritative_Read_Provider} \<union>
          (case action of Service_Maintenance (Exact_Enqueue origin) \<Rightarrow> {Primary_Publication_Dependency origin} | _ \<Rightarrow> {}), {})
     | Service_Slot resolved \<Rightarrow> ({Shared_Authority, Exact_Settlement_Slot (resolved_slot resolved)} \<union>
         (case resolved of Slot_Enqueue publication target \<Rightarrow> {Primary_Publication_Dependency (publication_origin publication)} | _ \<Rightarrow> {}),
          {Exact_Settlement_Slot (resolved_slot resolved)})
     | Service_Serial \<Rightarrow>
         ({Shared_Authority, Authoritative_Revision, Exact_Completion_History, Authoritative_Read_Provider},
          {Shared_Authority, Authoritative_Revision, Exact_Completion_History, Authoritative_Read_Provider}))"

definition compatible_service_actions where
  "compatible_service_actions first second s \<longleftrightarrow>
    (let (reads_first, writes_first) = service_access_footprint first s;
         (reads_second, writes_second) = service_access_footprint second s
     in writes_first \<inter> (reads_second \<union> writes_second) = {} \<and>
        writes_second \<inter> (reads_first \<union> writes_first) = {})"

lemma compatible_service_actions_are_symmetric:
  "compatible_service_actions a b s = compatible_service_actions b a s"
  by (simp add: compatible_service_actions_def Let_def conj_commute split: prod.splits)

lemma compatible_actions_have_no_shared_writer:
  assumes "compatible_service_actions a b s"
  shows "classify_service_action a s \<noteq> Service_Serial"
    "classify_service_action b s \<noteq> Service_Serial"
  using assms by (cases "classify_service_action a s"; cases "classify_service_action b s";
    auto simp: compatible_service_actions_def service_access_footprint_def Let_def split: retained_service_action.splits exact_action.splits resolved_settlement_action.splits)+

lemma compatible_settlement_writes_use_distinct_exact_slots:
  assumes "compatible_service_actions a b s"
    "classify_service_action a s = Service_Slot x" "classify_service_action b s = Service_Slot y"
  shows "resolved_slot x \<noteq> resolved_slot y"
  using assms by (auto simp: compatible_service_actions_def service_access_footprint_def Let_def split: prod.splits)

datatype scheduled_service_reply =
    Scheduled_Endpoint retained_service_reply
  | Scheduled_Settlement settlement_action_reply

context source_attestation
begin

definition schedule_service_step where
  "schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
     action s =
    (case action of Service_Maintenance maintenance \<Rightarrow>
       if is_settlement_action maintenance then
         let result = execute_settlement_action verified_ack maintenance (service_settlement s)
         in (replace_service_jobs (settlement_jobs (fst result)) s, Scheduled_Settlement (snd result))
       else let result = live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
            legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s
            in (fst result, Scheduled_Endpoint (snd result))
     | _ \<Rightarrow> let result = live_product_service_step directory policy read_policy authenticate verify verify_read endorse approve
            legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack action s
            in (fst result, Scheduled_Endpoint (snd result)))"

definition schedule_at_retained_state where
  "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
     connection action retained =
    (let result = schedule_service_step directory policy read_policy authenticate verify verify_read endorse approve
        legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
        action (reopen_retained_product connection retained)
     in (capture_retained_product (fst result), snd result))"

end

end
