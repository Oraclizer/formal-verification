theory Propagation_Queue
  imports Origin_Decisions
begin

section \<open>Secondary work is derived from an immutable primary record\<close>

type_synonym settlement_identity = "source_key \<times> nat"

record product_publication =
  publication_origin :: source_key
  publication_decision :: product_origin_decision

definition settlement_key where
  "settlement_key published = (publication_origin published, origin_commit_position (publication_decision published))"

definition primary_publication where
  "primary_publication s key =
    (let core = call_authority_state (product_calls (outcome_source (origin_outcomes s))) in
     case (origin_decisions s key, core_records core key) of
       (Some decision, Some recorded) \<Rightarrow>
         if key \<in> core_published core \<and> binding_key (origin_binding decision) = key \<and>
            terminal_core recorded = (origin_binding decision, origin_kind decision) \<and>
            terminal_effect_completed core recorded
         then Some \<lparr>publication_origin = key, publication_decision = decision\<rparr> else None
     | _ \<Rightarrow> None)"

datatype secondary_status = Secondary_Waiting | Secondary_In_Flight | Secondary_Completed

record product_secondary_job =
  secondary_publication :: product_publication
  secondary_target :: nat
  secondary_attempts :: nat
  secondary_state :: secondary_status

record product_secondary_ack =
  ack_settlement_key :: settlement_identity
  ack_publication :: product_publication
  ack_target :: nat

record settlement_world =
  settlement_primary :: origin_world
  settlement_target :: nat
  settlement_jobs :: "settlement_identity \<Rightarrow> product_secondary_job option"

definition initial_settlement_world where
  "initial_settlement_world target s = \<lparr>settlement_primary = s, settlement_target = target,
    settlement_jobs = (\<lambda>_. None)\<rparr>"

definition enqueue_secondary where
  "enqueue_secondary origin s =
    (case primary_publication (settlement_primary s) origin of None \<Rightarrow> s
    | Some published \<Rightarrow>
      let key = settlement_key published in
      if settlement_jobs s key \<noteq> None then s
      else s\<lparr>settlement_jobs := (settlement_jobs s)(key := Some
        \<lparr>secondary_publication = published, secondary_target = settlement_target s,
          secondary_attempts = 0, secondary_state = Secondary_Waiting\<rparr>)\<rparr>)"

definition update_secondary_job where
  "update_secondary_job key job s = s\<lparr>settlement_jobs := (settlement_jobs s)(key := Some job)\<rparr>"

definition dispatch_secondary where
  "dispatch_secondary key s =
    (case settlement_jobs s key of None \<Rightarrow> s
    | Some job \<Rightarrow> if secondary_state job = Secondary_Completed then s
      else update_secondary_job key (job\<lparr>secondary_attempts := Suc (secondary_attempts job),
        secondary_state := Secondary_In_Flight\<rparr>) s)"

definition fail_secondary where
  "fail_secondary key s =
    (case settlement_jobs s key of None \<Rightarrow> s
    | Some job \<Rightarrow> if secondary_state job = Secondary_In_Flight
      then update_secondary_job key (job\<lparr>secondary_state := Secondary_Waiting\<rparr>) s else s)"

definition exact_secondary_ack where
  "exact_secondary_ack ack job \<longleftrightarrow>
    ack_settlement_key ack = settlement_key (secondary_publication job) \<and>
    ack_publication ack = secondary_publication job \<and>
    ack_target ack = secondary_target job"

definition acknowledge_secondary where
  "acknowledge_secondary verified ack s =
    (let key = ack_settlement_key ack in case settlement_jobs s key of None \<Rightarrow> s
     | Some job \<Rightarrow> if verified ack \<and> exact_secondary_ack ack job \<and> secondary_attempts job > 0
        then update_secondary_job key (job\<lparr>secondary_state := Secondary_Completed\<rparr>) s else s)"

lemma no_secondary_job_before_primary_publication:
  "primary_publication (settlement_primary s) origin = None \<Longrightarrow> enqueue_secondary origin s = s"
  by (simp add: enqueue_secondary_def)

lemma primary_publication_contains_exact_authority_record:
  assumes "primary_publication s key = Some published"
  shows "publication_origin published = key \<and> origin_decisions s key = Some (publication_decision published)"
  using assms by (auto simp: primary_publication_def Let_def split: option.splits if_splits prod.splits)

lemma secondary_steps_preserve_primary:
  "settlement_primary (enqueue_secondary origin s) = settlement_primary s"
  "settlement_primary (dispatch_secondary key s) = settlement_primary s"
  "settlement_primary (fail_secondary key s) = settlement_primary s"
  "settlement_primary (acknowledge_secondary verified ack s) = settlement_primary s"
  by (auto simp: enqueue_secondary_def dispatch_secondary_def fail_secondary_def acknowledge_secondary_def
      update_secondary_job_def Let_def split: option.splits if_splits)

lemma retry_keeps_the_exact_publication_under_the_same_key:
  assumes "settlement_jobs s key = Some job" "secondary_state job \<noteq> Secondary_Completed"
  shows "settlement_jobs (dispatch_secondary key (fail_secondary key s)) key =
    Some (job\<lparr>secondary_attempts := Suc (secondary_attempts job), secondary_state := Secondary_In_Flight\<rparr>)"
  using assms by (cases "secondary_state job")
    (simp_all add: dispatch_secondary_def fail_secondary_def update_secondary_job_def)

lemma wrong_ack_cannot_complete_a_secondary_job:
  assumes "settlement_jobs s (ack_settlement_key ack) = Some job" "\<not> exact_secondary_ack ack job"
  shows "acknowledge_secondary verified ack s = s"
  using assms by (simp add: acknowledge_secondary_def Let_def)

lemma exact_verified_ack_completes_the_recorded_job:
  assumes "settlement_jobs s (ack_settlement_key ack) = Some job" "exact_secondary_ack ack job"
    "verified ack" "secondary_attempts job > 0"
  shows "settlement_jobs (acknowledge_secondary verified ack s) (ack_settlement_key ack) =
    Some (job\<lparr>secondary_state := Secondary_Completed\<rparr>)"
  using assms by (simp add: acknowledge_secondary_def update_secondary_job_def Let_def)

end
