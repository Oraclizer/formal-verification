theory Request_Example
  imports Scheduler_Examples
begin

definition sample_event ::
  "nat \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition"
where
  "sample_event n =
    (if n = 0 then \<lparr>source_state = ordinary_admitted, step_action = Submit urgent_packet,
         step_outcome = Accepted 102, target_state = priority_admitted\<rparr>
     else if n = 1 then \<lparr>source_state = priority_admitted, step_action = Honest_Service,
         step_outcome = Internal (Served_Regulation 102 9), target_state = priority_handled\<rparr>
     else if n = 2 then \<lparr>source_state = priority_handled, step_action = Honest_Service,
         step_outcome = Internal (Served_Ordinary 101), target_state = ordinary_handled\<rparr>
     else \<lparr>source_state = ordinary_handled, step_action = Honest_Service,
         step_outcome = Rejected Empty_Queue, target_state = ordinary_handled\<rparr>)"

lemma work_cleared_produces_an_empty_turn:
  "scheduler_step ordinary_handled Honest_Service (Rejected Empty_Queue) ordinary_handled"
  by (simp add: scheduler_reduction packet_example
      ordinary_admitted_def priority_admitted_def priority_handled_def ordinary_handled_def)

lemma sample_steps_execute:
  "step_occurs scheduler_step (sample_event n)"
  using regulation_then_exact_ordinary_completion(1,3,7) work_cleared_produces_an_empty_turn
  by (auto simp: step_occurs_def sample_event_def split: if_splits)

lemma sample_steps_link:
  "target_state (sample_event n) = source_state (sample_event (Suc n))"
  by (auto simp: sample_event_def split: if_splits)

lemma sample_infinite_run:
  "infinite_run scheduler_step {ordinary_admitted} UNIV sample_event"
proof -
  have first: "source_state (sample_event 0) = ordinary_admitted" by (simp add: sample_event_def)
  with sample_steps_execute sample_steps_link show ?thesis by (simp add: infinite_run_def)
qed

lemma sample_interfering_positions:
  "{i. spends_priority (sample_event i)} = {1}"
  by (auto simp: sample_event_def spends_priority_def split: if_splits)

lemma sample_honest_opportunities:
  "\<exists>j\<ge>i. step_action (sample_event j) = Honest_Service"
  by (rule exI[of _ "Suc i"]) (simp add: sample_event_def)

theorem source_selected_ordinary_packet_is_really_served:
  "\<exists>j. served_ordinary (packet_identity ordinary_packet) (sample_event j) \<and>
     ordinary_receipts (target_state (sample_event j)) (packet_identity ordinary_packet) = Some ordinary_packet"
proof -
  have origin: "coherent_ordinary_queue scheduler_example"
    by (simp add: coherent_ordinary_queue_def ordinary_shape_def ordinary_ids_def scheduler_example_def)
  have accept:
    "scheduler_step scheduler_example (Submit ordinary_packet) (Accepted (packet_identity ordinary_packet)) ordinary_admitted"
    using rejected_spam_does_not_poison_the_real_id(3) by (simp add: ordinary_packet_def)
  have ordinary: "ordinary_body (packet_contents ordinary_packet)" by (simp add: ordinary_packet_def)
  have interference: "finite {i. spends_priority (sample_event i)}" by (simp add: sample_interfering_positions)
  show ?thesis by (rule admitted_packet_is_served_under_finite_interference[OF origin accept ordinary
    sample_infinite_run interference sample_honest_opportunities])
qed

lemma sample_priority_step_really_raises_its_case:
  "escalation_slice {9} (sample_event i)"
proof (cases "i = 1")
  case True
  have chosen: "next_regulation priority_admitted = Some urgent_packet"
    by (simp add: scheduler_reduction packet_example ordinary_admitted_def priority_admitted_def)
  from True chosen show ?thesis
    by (auto simp: escalation_slice_def raises_a_case_def sample_event_def urgent_packet_def)
next
  case False
  with sample_interfering_positions have "\<not> spends_priority (sample_event i)" by auto
  then show ?thesis by (simp add: escalation_slice_def)
qed

theorem source_selected_packet_served_under_fixed_escalation:
  "\<exists>j. served_ordinary (packet_identity ordinary_packet) (sample_event j) \<and>
     ordinary_receipts (target_state (sample_event j)) (packet_identity ordinary_packet) = Some ordinary_packet"
proof -
  have origin: "coherent_ordinary_queue scheduler_example"
    by (simp add: coherent_ordinary_queue_def ordinary_shape_def ordinary_ids_def scheduler_example_def)
  have accept:
    "scheduler_step scheduler_example (Submit ordinary_packet) (Accepted (packet_identity ordinary_packet)) ordinary_admitted"
    using rejected_spam_does_not_poison_the_real_id(3) by (simp add: ordinary_packet_def)
  have ordinary: "ordinary_body (packet_contents ordinary_packet)" by (simp add: ordinary_packet_def)
  have cap: "active_case_levels {9} (source_state (sample_event 0))"
    by (simp add: active_case_levels_def sample_event_def scheduler_reduction packet_example ordinary_admitted_def)
  have finite_cases: "finite ({9} :: nat set)" by simp
  show ?thesis
    by (rule admitted_packet_is_served_under_fixed_case_escalation[
      OF origin accept ordinary sample_infinite_run finite_cases cap
      sample_priority_step_really_raises_its_case sample_honest_opportunities])
qed

section \<open>Staged deployment with a signed context update\<close>

text \<open>The rollout gate is handled before the install request is admitted.
  A verified policy rotation occurs between install admission and service.
  The deployment consumer needs both the previously issued gate receipt
  and the exact manifest receipt produced by the request completion proof.\<close>

definition manifest_packet :: packet
where
  "manifest_packet = ordinary_packet\<lparr>packet_identity := 202, packet_contents := Ordinary_Work 777\<rparr>"

definition deployment_origin :: scheduler_state where
  "deployment_origin = scheduler_example\<lparr>signed_packets := insert manifest_packet (signed_packets scheduler_example)\<rparr>"

definition gate_admitted :: scheduler_state where
  "gate_admitted = snd (admit deployment_origin urgent_packet)"

definition gate_completed :: scheduler_state where
  "gate_completed = snd (schedule gate_admitted)"

definition manifest_admitted :: scheduler_state where
  "manifest_admitted = snd (admit gate_completed manifest_packet)"

definition deployment_rotated :: scheduler_state where
  "deployment_rotated = snd (run_scheduler manifest_admitted (Rotate_Context 5 4 9 9))"

definition manifest_completed :: scheduler_state where
  "manifest_completed = snd (schedule deployment_rotated)"

lemmas deployment_setup = manifest_packet_def deployment_origin_def gate_admitted_def
  gate_completed_def manifest_admitted_def deployment_rotated_def manifest_completed_def

lemma deployment_execution_controls:
  "scheduler_step deployment_origin (Submit urgent_packet) (Accepted 102) gate_admitted"
  "scheduler_step gate_admitted Honest_Service (Internal (Served_Regulation 102 9)) gate_completed"
  "regulation_receipts gate_completed 102 = Some urgent_packet"
  "scheduler_step gate_completed (Submit manifest_packet) (Accepted 202) manifest_admitted"
  "scheduler_step manifest_admitted (Rotate_Context 5 4 9 9) (Internal Snapshot_Changed) deployment_rotated"
  "scheduler_step deployment_rotated Honest_Service (Internal (Served_Ordinary 202)) manifest_completed"
  "scheduler_step manifest_completed Honest_Service (Rejected Empty_Queue) manifest_completed"
  by (simp_all add: deployment_setup scheduler_reduction packet_example)

definition deployment_event ::
  "nat \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition"
where
  "deployment_event n =
    (if n = 0 then \<lparr>source_state = manifest_admitted, step_action = Rotate_Context 5 4 9 9,
         step_outcome = Internal Snapshot_Changed, target_state = deployment_rotated\<rparr>
     else if n = 1 then \<lparr>source_state = deployment_rotated, step_action = Honest_Service,
         step_outcome = Internal (Served_Ordinary 202), target_state = manifest_completed\<rparr>
     else \<lparr>source_state = manifest_completed, step_action = Honest_Service,
         step_outcome = Rejected Empty_Queue, target_state = manifest_completed\<rparr>)"

lemma deployment_run:
  "infinite_run scheduler_step {manifest_admitted} UNIV deployment_event"
proof -
  have start: "source_state (deployment_event 0) = manifest_admitted"
    by (simp add: deployment_event_def)
  have moves: "\<And>n. step_occurs scheduler_step (deployment_event n)"
    using deployment_execution_controls(5-7)
    by (auto simp: deployment_event_def step_occurs_def split: if_splits)
  have links: "\<And>n. target_state (deployment_event n) = source_state (deployment_event (Suc n))"
    by (auto simp: deployment_event_def split: if_splits)
  from start moves links show ?thesis by (simp add: infinite_run_def)
qed

definition observed_manifest :: "scheduler_state \<Rightarrow> packet option"
where "observed_manifest s = ordinary_receipts s 202"

datatype deployment_observation = Deployment_Pending | Manifest_Live nat

definition deployment_view :: "scheduler_state \<Rightarrow> deployment_observation"
where
  "deployment_view s =
    (if regulation_receipts s 102 \<noteq> Some urgent_packet then Deployment_Pending
     else case observed_manifest s of
       None \<Rightarrow> Deployment_Pending
     | Some p \<Rightarrow> (case packet_contents p of Ordinary_Work digest \<Rightarrow> Manifest_Live digest
         | _ \<Rightarrow> Deployment_Pending))"

lemma admitted_manifest_alone_cannot_unlock_deployment:
  "deployment_view manifest_admitted = Deployment_Pending"
  by (simp add: deployment_view_def observed_manifest_def deployment_setup scheduler_reduction packet_example)

theorem deployment_consumer_uses_the_request_completion_receipt:
  "\<exists>j. served_ordinary (packet_identity manifest_packet) (deployment_event j) \<and>
     deployment_view (target_state (deployment_event j)) = Manifest_Live 777"
proof -
  have origin: "coherent_ordinary_queue gate_completed"
    by (simp add: coherent_ordinary_queue_def ordinary_shape_def ordinary_ids_def
      deployment_setup scheduler_reduction packet_example)
  have manifest_accept: "scheduler_step gate_completed (Submit manifest_packet)
    (Accepted (packet_identity manifest_packet)) manifest_admitted"
    using deployment_execution_controls(4) by (simp add: manifest_packet_def ordinary_packet_def)
  have ordinary: "ordinary_body (packet_contents manifest_packet)" by (simp add: manifest_packet_def)
  have "\<And>i. \<not> spends_priority (deployment_event i)"
    by (auto simp: deployment_event_def spends_priority_def split: if_splits)
  then have interference: "finite {i. spends_priority (deployment_event i)}" by simp
  have opportunities: "\<And>i. \<exists>j\<ge>i. step_action (deployment_event j) = Honest_Service"
  proof -
    fix i
    show "\<exists>j\<ge>i. step_action (deployment_event j) = Honest_Service"
      by (rule exI[of _ "Suc i"]) (simp add: deployment_event_def)
  qed
  from admitted_packet_is_served_under_finite_interference[
    OF origin manifest_accept ordinary deployment_run interference opportunities] obtain j where
    applied: "served_ordinary (packet_identity manifest_packet) (deployment_event j)"
    and installed: "ordinary_receipts (target_state (deployment_event j)) (packet_identity manifest_packet) = Some manifest_packet"
    by blast
  have gate_kept: "regulation_receipts (target_state (deployment_event j)) 102 = Some urgent_packet"
    by (simp add: deployment_event_def deployment_setup scheduler_reduction packet_example)
  show ?thesis
  proof (rule exI[of _ j])
    from applied installed gate_kept show
      "served_ordinary (packet_identity manifest_packet) (deployment_event j) \<and>
       deployment_view (target_state (deployment_event j)) = Manifest_Live 777"
      by (simp add: deployment_view_def observed_manifest_def manifest_packet_def ordinary_packet_def)
  qed
qed

type_synonym release_catalogue = "nat \<Rightarrow> nat option"

definition publish_observed_manifest ::
  "scheduler_state \<Rightarrow> nat \<Rightarrow> release_catalogue \<Rightarrow> release_catalogue"
where
  "publish_observed_manifest s release existing =
    (case deployment_view s of Deployment_Pending \<Rightarrow> existing
     | Manifest_Live digest \<Rightarrow> existing(release \<mapsto> digest))"

theorem deployment_application_publishes_only_the_observed_manifest:
  "\<exists>j. served_ordinary (packet_identity manifest_packet) (deployment_event j) \<and>
    publish_observed_manifest (target_state (deployment_event j)) release existing release = Some 777 \<and>
    (\<forall>other. other \<noteq> release \<longrightarrow>
      publish_observed_manifest (target_state (deployment_event j)) release existing other = existing other)"
proof -
  from deployment_consumer_uses_the_request_completion_receipt obtain j where
    "served_ordinary (packet_identity manifest_packet) (deployment_event j)"
    "deployment_view (target_state (deployment_event j)) = Manifest_Live 777" by blast
  then show ?thesis by (intro exI[of _ j]) (simp add: publish_observed_manifest_def)
qed

lemma same_id_wrong_manifest_exposes_the_other_digest:
  "deployment_view (manifest_completed\<lparr>ordinary_receipts := (ordinary_receipts manifest_completed)
    (202 \<mapsto> manifest_packet\<lparr>packet_contents := Ordinary_Work 888\<rparr>)\<rparr>) = Manifest_Live 888"
  by (simp add: deployment_view_def observed_manifest_def deployment_setup scheduler_reduction packet_example)

end
