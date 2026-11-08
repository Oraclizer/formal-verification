theory Wire_Code_Dispatch
  imports Wire_Code_Path_Guards
begin

datatype code_dispatch_operation = Code_Dispatch_Receive | Code_Dispatch_Resolve_Debit

definition code_dispatch_start :: "nat \<Rightarrow> nat option \<Rightarrow> bool" where
  "code_dispatch_start max_wait checked_deadline \<longleftrightarrow> max_wait \<noteq> 0 \<and> checked_deadline \<noteq> None"

lemma a_started_dispatcher_has_a_positive_representable_wait:
  "code_dispatch_start max_wait checked_deadline \<Longrightarrow>
    0 < max_wait \<and> (\<exists>limit. checked_deadline = Some limit)"
  by (auto simp: code_dispatch_start_def split: option.splits)

definition code_dispatch_submit :: "nat \<Rightarrow> wire_bytes \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (code_path_refusal + nat)" where
  "code_dispatch_submit frame_limit packet now checked_deadline caller_deadline enqueued =
    (if length packet > frame_limit then Inl (Code_Path_Validation Invalid_Wire_Format)
     else case checked_deadline of None \<Rightarrow> Inl Code_Path_Unresolved | Some limit \<Rightarrow>
       let deadline = min caller_deadline limit in
       if now \<ge> deadline \<or> \<not> enqueued then Inl Code_Path_Unresolved else Inr deadline)"

lemma an_oversize_dispatch_is_refused_before_queueing:
  "length packet > frame_limit \<Longrightarrow>
    code_dispatch_submit frame_limit packet now checked_deadline caller_deadline enqueued =
      Inl (Code_Path_Validation Invalid_Wire_Format)"
  by (simp add: code_dispatch_submit_def)

lemma a_queued_dispatch_uses_the_smaller_caller_or_configured_deadline:
  assumes "code_dispatch_submit frame_limit packet now checked_deadline caller_deadline enqueued = Inr deadline"
  shows "deadline \<le> caller_deadline \<and> now < deadline \<and> enqueued \<and>
    (\<exists>limit. checked_deadline = Some limit \<and> deadline = min caller_deadline limit)"
  using assms by (auto simp: code_dispatch_submit_def Let_def split: option.splits if_splits)

lemma an_unqueued_in_range_dispatch_is_unresolved:
  assumes "length packet \<le> frame_limit" "\<not> enqueued"
  shows "code_dispatch_submit frame_limit packet now checked_deadline caller_deadline enqueued = Inl Code_Path_Unresolved"
  using assms by (cases checked_deadline) (simp_all add: code_dispatch_submit_def Let_def)

definition code_wait_for_ordered_reply :: "'error \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('error + 'reply) option \<Rightarrow> nat \<Rightarrow> ('error + 'reply)" where
  "code_wait_for_ordered_reply unresolved before deadline received after =
    (if before \<ge> deadline then Inl unresolved
     else case received of None \<Rightarrow> Inl unresolved | Some result \<Rightarrow>
       if after \<ge> deadline then Inl unresolved else result)"

lemma a_reply_after_the_wait_deadline_is_unresolved_even_if_it_arrived:
  "after \<ge> deadline \<Longrightarrow>
    code_wait_for_ordered_reply unresolved before deadline (Some result) after = Inl unresolved"
  by (simp add: code_wait_for_ordered_reply_def)

lemma a_live_received_worker_result_keeps_its_exact_error_or_response:
  assumes "before < deadline" "after < deadline"
  shows "code_wait_for_ordered_reply unresolved before deadline (Some result) after = result"
  using assms by (simp add: code_wait_for_ordered_reply_def)

definition code_dispatch_worker where
  "code_dispatch_worker receive resolve operation channel token (packet::wire_bytes) state =
    (case operation of Code_Dispatch_Receive \<Rightarrow>
       receive channel Identity_Normal token packet packet
         \<lparr>delivery_cancelled = False,delivery_service_deadline = None\<rparr> False state
     | Code_Dispatch_Resolve_Debit \<Rightarrow> resolve channel token packet packet False state)"

lemma the_dispatch_worker_packet_credential_is_the_owned_packet:
  "code_matches_signed_packet packet packet"
  by (rule the_dispatcher_packet_identity_test_is_not_a_cryptographic_signature_test)

lemma the_dispatch_resolver_does_not_close_an_unresolved_original:
  "code_dispatch_worker receive resolve Code_Dispatch_Resolve_Debit channel token packet state =
    resolve channel token packet packet False state"
  by (simp add: code_dispatch_worker_def)

definition code_worker_then_wait where
  "code_worker_then_wait unresolved worker state before deadline after =
    (let (updated,result) = worker state in
     (updated,code_wait_for_ordered_reply unresolved before deadline (Some result) after))"

theorem an_expired_wait_does_not_roll_back_the_workers_retained_state:
  "fst (code_worker_then_wait unresolved worker state before deadline after) = fst (worker state)"
  by (simp add: code_worker_then_wait_def Let_def split: prod.splits)

text \<open>
  Source: ed25519/dispatch.rs start/submit/worker and wire.rs
  wait_for_ordered_wire_reply. checked_deadline is the actual checked_add
  result supplied by the clock/runtime adapter; enqueued and received are
  the actual bounded-channel observations. Thread creation, monotonic time,
  bounded channels and allocation remain named runtime boundaries.
  receive/resolve must be instantiated with the separately checked source
  response-path functions. The worker-state theorem is about that explicit
  composition; it does not prove OS scheduling or eventual completion.
\<close>

end
