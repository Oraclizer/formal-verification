theory Stored_Service_Observation
  imports Approved_Scoped_Execution
begin

record service_snapshot =
  store_cut :: nat
  observed_scheduler :: scheduler_state

datatype attempt_outcome = Compare_Conflict | Service_Result scheduler_result

definition signed_packets_by_turn :: "(service_turn \<Rightarrow> packet option) \<Rightarrow> (service_turn \<times> packet) set"
where
  "signed_packets_by_turn orders = {(turn,p). orders turn = Some p}"

lemma the_same_signed_turn_names_only_one_packet:
  assumes "(turn,p) \<in> signed_packets_by_turn orders" "(turn,q) \<in> signed_packets_by_turn orders"
  shows "p = q"
  using assms by (simp add: signed_packets_by_turn_def)

definition try_service_at ::
  "verified_inputs \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> (service_turn \<Rightarrow> packet option) \<Rightarrow>
   service_snapshot \<Rightarrow> service_snapshot \<Rightarrow> service_turn \<Rightarrow> packet \<Rightarrow>
   attempt_outcome \<times> scheduler_state"
where
  "try_service_at inputs signer orders expected current turn p =
    (if expected \<noteq> current then (Compare_Conflict, observed_scheduler current)
     else case scoped_service inputs signer (signed_packets_by_turn orders) (observed_scheduler current) turn p of
       (outcome, t) \<Rightarrow> (Service_Result outcome, t))"

lemma changed_read_cut_compares_before_service:
  assumes "expected \<noteq> current"
  shows "try_service_at inputs signer orders expected current turn p =
    (Compare_Conflict, observed_scheduler current)"
  using assms by (simp add: try_service_at_def)

lemma fresh_read_at_current_cut_retains_the_old_signed_order_when_eligible:
  fixes earlier_cut later_cut :: nat
  assumes "earlier_cut \<noteq> later_cut"
  defines "expected \<equiv> \<lparr>store_cut = earlier_cut, observed_scheduler = first_update\<rparr>"
  defines "concurrent \<equiv> \<lparr>store_cut = later_cut, observed_scheduler = second_update\<rparr>"
  defines "signed_b \<equiv> (\<lambda>turn. if turn = current_turn then Some regulation_b else None)"
  shows "planned (authorized_view unapproved first_update) = Some regulation_b"
    and "planned (authorized_view unapproved second_update) = Some regulation_b"
    and "try_service_at unapproved (\<lambda>_. Some 2) signed_b expected concurrent current_turn regulation_b =
      (Compare_Conflict, second_update)"
    and "try_service_at unapproved (\<lambda>_. Some 2) signed_b concurrent concurrent current_turn regulation_b =
      (Service_Result (Internal (Served_Regulation fixture_actor_b fixture_case_b)), b_served)"
  using assms
  by (simp_all add: expected_def concurrent_def signed_b_def try_service_at_def
      scoped_service_def signed_packets_by_turn_def planned_def authorized_view_def current_turn_def
      qualified_turn_def mixed_steps)

datatype sequence_observation = Replayed_Receipt packet | Compared_Attempt attempt_outcome

definition exact_saved_packet :: "scheduler_state \<Rightarrow> packet \<Rightarrow> bool" where
  "exact_saved_packet s p \<longleftrightarrow>
    (if ordinary_body (packet_contents p) then ordinary_receipts s (packet_identity p) = Some p
     else regulation_receipts s (packet_identity p) = Some p)"

definition observe_sequence ::
  "verified_inputs \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> (service_turn \<Rightarrow> packet option) \<Rightarrow>
   (service_turn \<Rightarrow> packet option) \<Rightarrow> service_snapshot \<Rightarrow> service_snapshot \<Rightarrow>
   service_turn \<Rightarrow> packet \<Rightarrow> sequence_observation \<times> scheduler_state"
where
  "observe_sequence inputs signer orders retained expected current turn p =
    (if retained turn = Some p \<and> exact_saved_packet (observed_scheduler current) p
     then (Replayed_Receipt p, observed_scheduler current)
     else case try_service_at inputs signer orders expected current turn p of
       (outcome,t) \<Rightarrow> (Compared_Attempt outcome,t))"

lemma an_exact_executed_order_is_replayed_before_a_new_compare:
  assumes "retained turn = Some p" "exact_saved_packet (observed_scheduler current) p"
  shows "observe_sequence inputs signer orders retained expected current turn p =
      (Replayed_Receipt p, observed_scheduler current)"
  using assms by (simp add: observe_sequence_def)

lemma the_observed_regulatory_retry_returns_the_exact_body_without_a_new_effect:
  fixes replay_cut :: nat
  defines "current \<equiv> \<lparr>store_cut = replay_cut, observed_scheduler = b_served\<rparr>"
  defines "retained_b \<equiv> (\<lambda>turn. if turn = current_turn then Some regulation_b else None)"
  shows "observe_sequence unapproved (\<lambda>_. Some 2) retained_b retained_b current current current_turn regulation_b
    = (Replayed_Receipt regulation_b, b_served)"
  using assms
  by (simp add: observe_sequence_def exact_saved_packet_def current_def retained_b_def mixed_steps)

lemma an_uncommitted_order_still_refuses_a_raced_write:
  assumes "expected \<noteq> current" "retained turn \<noteq> Some p"
  shows "observe_sequence inputs signer orders retained expected current turn p =
     (Compared_Attempt Compare_Conflict, observed_scheduler current)"
  using assms by (simp add: observe_sequence_def try_service_at_def)

text \<open>The read boundary includes a privileged read of an already durable
receipt or disclosure of an ID's disposition. Retained admission identity is
the accepted packet, independent of receipt allocation and priority eligibility.\<close>

definition read_superseded ::
  "(nat \<Rightarrow> packet option) \<Rightarrow> scheduler_state \<Rightarrow> nat \<Rightarrow> scheduler_state \<Rightarrow> bool"
where
  "read_superseded admitted s q t \<longleftrightarrow>
    (t = s \<and> (\<exists>p. admitted q = Some p \<and> packet_identity p = q
       \<and> \<not> ordinary_body (packet_contents p) \<and> q \<in> dedup_ids s \<and> permanently_stale s p
       \<and> p \<notin> set (regulatory_queue s) \<and> regulation_receipts s q = None))"

lemma superseded_projection_requires_the_retained_identity:
  "read_superseded admitted s q t \<Longrightarrow> (\<exists>p. admitted q = Some p \<and> packet_identity p = q)"
  by (auto simp: read_superseded_def)

lemma a_retained_ordinary_request_is_never_reported_superseded:
  assumes "admitted q = Some p" "ordinary_body (packet_contents p)"
  shows "\<not> read_superseded admitted s q t"
  using assms by (auto simp: read_superseded_def)

lemma retired_case_in_the_mixed_trace_has_the_original_admission_and_no_effect:
  "read_superseded (\<lambda>q. if q = fixture_actor_a then Some regulation_a else None)
     (retire_stale second_update) fixture_actor_a (retire_stale second_update)"
  by (simp add: read_superseded_def mixed_steps retire_stale_def permanently_stale_def)

end
