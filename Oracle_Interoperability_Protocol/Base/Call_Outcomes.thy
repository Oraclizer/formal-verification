theory Call_Outcomes
  imports Lock_Product_Run
begin

section \<open>Authoritative request and result binding\<close>

datatype product_outcome =
    Authority_Reply finality_reply
  | Authority_Rejected
  | Authority_Busy
  | Authority_Unavailable

record product_call_payload =
  payload_envelope :: product_envelope
  payload_credential :: "product_lock_credential option"
  payload_origin_epoch :: nat

record product_result_entry =
  result_payload :: product_call_payload
  result_outcome :: product_outcome

record outcome_world =
  outcome_source :: product_world
  outcome_entries :: "client_call_id \<Rightarrow> product_result_entry option"
  outcome_completed :: "client_call_id set"

definition initial_outcome_world where
  "initial_outcome_world s = \<lparr>outcome_source = s, outcome_entries = (\<lambda>_. None), outcome_completed = {}\<rparr>"

fun normalized_authority_reply where
  "normalized_authority_reply Finality_Rejected = Authority_Rejected"
| "normalized_authority_reply (Protocol_Response Request_Rejected) = Authority_Rejected"
| "normalized_authority_reply (Protocol_Response Reservation_Busy) = Authority_Busy"
| "normalized_authority_reply reply = Authority_Reply reply"

definition result_access_bound where
  "result_access_bound verified who call_id payload s \<longleftrightarrow>
    verified who call_id payload \<and>
    product_identity_bound who call_id (payload_envelope payload) (outcome_source s)"

definition store_product_result where
  "store_product_result call_id payload outcome next s = s\<lparr>outcome_source := next,
    outcome_entries := (outcome_entries s)(call_id := Some \<lparr>result_payload = payload, result_outcome = outcome\<rparr>)\<rparr>"

context source_attestation
begin

definition submit_new_authoritative_call where
  "submit_new_authoritative_call permitted maintainers registered entry who call_id payload s =
    (let before = outcome_source s; calls = product_calls before;
         next = lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered
           (Lock_Submit entry who call_id (payload_envelope payload) (payload_credential payload)) before
     in if call_invocations calls call_id \<noteq> None \<or> call_authority_results calls call_id \<noteq> None \<or>
           call_local_status calls \<noteq> Endpoint_Up then s
        else if call_connection calls \<noteq> Authority_Connected
        then store_product_result call_id payload Authority_Unavailable before s
        else case call_authority_results (product_calls next) call_id of
          None \<Rightarrow> store_product_result call_id payload Authority_Rejected next s
        | Some (_, reply, _) \<Rightarrow> store_product_result call_id payload (normalized_authority_reply reply) next s)"

definition submit_authoritative_call where
  "submit_authoritative_call permitted verified maintainers registered entry who call_id payload s =
    (if result_access_bound verified who call_id payload s \<and> outcome_entries s call_id = None
     then submit_new_authoritative_call permitted maintainers registered entry who call_id payload s else s)"

lemma authoritative_call_retry_does_not_repeat_effect:
  "outcome_entries s call_id = Some recorded \<Longrightarrow>
    submit_authoritative_call permitted verified maintainers registered entry who call_id payload s = s"
  by (simp add: submit_authoritative_call_def)

lemma authoritative_call_keeps_older_results:
  assumes "outcome_entries s recorded_id = Some recorded"
  shows "outcome_entries (submit_authoritative_call permitted verified maintainers registered entry who call_id payload s)
    recorded_id = Some recorded"
proof (cases "call_id = recorded_id")
  case True
  then show ?thesis using assms by (simp add: authoritative_call_retry_does_not_repeat_effect)
next
  case False
  then show ?thesis using assms
    by (auto simp: submit_authoritative_call_def submit_new_authoritative_call_def store_product_result_def Let_def
        split: option.splits prod.splits if_splits)
qed

lemma no_outcome_written_for_unbound_identity:
  "\<not> result_access_bound verified who call_id payload s \<Longrightarrow>
    submit_authoritative_call permitted verified maintainers registered entry who call_id payload s = s"
  by (simp add: submit_authoritative_call_def)

lemma denied_route_cannot_change_the_public_source:
  assumes denied: "\<not> permitted entry who (envelope_command (payload_envelope payload))"
  shows "outcome_source (submit_authoritative_call permitted verified maintainers registered entry who call_id payload s) = outcome_source s"
proof -
  have step: "lock_product_step permitted (\<lambda>_ _ _ _. True) maintainers registered
      (Lock_Submit entry who call_id (payload_envelope payload) (payload_credential payload)) (outcome_source s) = outcome_source s"
    using denied by (simp add: submit_lock_entry_def lock_submission_allowed_def)
  show ?thesis
    by (simp del: lock_product_step.simps
      add: submit_authoritative_call_def submit_new_authoritative_call_def store_product_result_def Let_def step
      split: option.splits prod.splits if_splits)
qed

end

section \<open>Collection and exact completion\<close>

fun final_effect_key where
  "final_effect_key (Client_Protocol endpoint index (Deliver_Intent route r))
      (Authority_Reply (Protocol_Response (Delivery_Response (New_Credit b)))) = Some (binding_key b)"
| "final_effect_key (Client_Protocol endpoint index (Deliver_Intent route r))
      (Authority_Reply (Protocol_Response (Delivery_Response (Duplicate_Credit b)))) = Some (binding_key b)"
| "final_effect_key (Client_Protocol endpoint index (Return_Intent r g versions))
      (Authority_Reply (Protocol_Response Reservation_Released)) = Some (binding_key (request_binding r))"
| "final_effect_key command outcome = None"

definition result_completion_ready where
  "result_completion_ready recorded s \<longleftrightarrow>
    (let envelope = payload_envelope (result_payload recorded); before = outcome_source s;
         core = call_authority_state (product_calls before);
         rs = machine_state (core_parent core)
     in case final_effect_key (envelope_command envelope) (result_outcome recorded) of None \<Rightarrow> True
      | Some key \<Rightarrow> key \<in> core_published core \<and> asset_owner rs (envelope_asset envelope) \<noteq> Some key)"

definition read_authoritative_result where
  "read_authoritative_result verified who call_id payload s =
    (if result_access_bound verified who call_id payload s then
      case outcome_entries s call_id of None \<Rightarrow> None
      | Some recorded \<Rightarrow> if result_payload recorded = payload \<and> result_completion_ready recorded s
        then Some (result_outcome recorded) else None
     else None)"

definition complete_authoritative_result where
  "complete_authoritative_result verified who call_id payload s =
    (if call_local_status (product_calls (outcome_source s)) \<noteq> Endpoint_Up then (s, None)
     else case read_authoritative_result verified who call_id payload s of None \<Rightarrow> (s, None)
      | Some reply \<Rightarrow> (s\<lparr>outcome_completed := insert call_id (outcome_completed s)\<rparr>, Some reply))"

lemma crashed_endpoint_cannot_expose_a_completion:
  "call_local_status (product_calls (outcome_source s)) = Endpoint_Down \<Longrightarrow>
    complete_authoritative_result verified who call_id payload s = (s, None)"
  by (simp add: complete_authoritative_result_def)

lemma exact_retry_reads_the_committed_outcome:
  assumes "result_access_bound verified who call_id payload s" "outcome_entries s call_id = Some recorded"
    "result_payload recorded = payload" "result_completion_ready recorded s"
  shows "read_authoritative_result verified who call_id payload s = Some (result_outcome recorded)"
  using assms by (simp add: read_authoritative_result_def)

lemma conflicting_retry_cannot_read_the_old_outcome:
  assumes "outcome_entries s call_id = Some recorded" "result_payload recorded \<noteq> payload"
  shows "read_authoritative_result verified who call_id payload s = None"
  using assms by (simp add: read_authoritative_result_def)

lemma completed_result_has_a_committed_exact_binding:
  assumes "snd (complete_authoritative_result verified who call_id payload s) = Some reply"
  shows "\<exists>recorded. outcome_entries s call_id = Some recorded \<and> result_payload recorded = payload \<and>
    result_outcome recorded = reply \<and> result_completion_ready recorded s"
  using assms by (auto simp: complete_authoritative_result_def read_authoritative_result_def
      split: option.splits if_splits)

lemma completion_is_idempotent:
  "complete_authoritative_result verified who call_id payload
     (fst (complete_authoritative_result verified who call_id payload s)) =
   complete_authoritative_result verified who call_id payload s"
  by (auto simp: complete_authoritative_result_def read_authoritative_result_def result_access_bound_def
      result_completion_ready_def Let_def split: option.splits if_splits)

end
