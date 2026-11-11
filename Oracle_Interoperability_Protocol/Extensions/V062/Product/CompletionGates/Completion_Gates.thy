theory Completion_Gates
  imports "OIP_Product_Base.Outcome_Gates"
begin

section \<open>Retained ordinary result and publication selection\<close>

text \<open>
  The projection is taken after the current caller and exact receipt checks.
  The origin row supplies the exact decision, settled position and published
  position. Authorization, source attestation, and storage are separate.
\<close>

type_synonym 'decision cg_origin_row = "'decision option \<times> nat option \<times> nat option"

fun cg_present where
  "cg_present None = False"
| "cg_present (Some value) = True"

fun cg_publication :: "'decision cg_origin_row option \<Rightarrow> 'decision option" where
  "cg_publication None = None"
| "cg_publication (Some (decision, settled, published)) =
    (if cg_present published \<and> cg_present settled then decision else None)"

definition cg_gate_with where
  "cg_gate_with require_publication require_release final origin lock_owner row \<longleftrightarrow>
    (\<not> final \<or> ((\<not> require_publication \<or> cg_present (cg_publication row)) \<and>
        (\<not> require_release \<or> lock_owner \<noteq> Some origin)))"

abbreviation cg_ready where
  "cg_ready \<equiv> cg_gate_with True True"

lemma cg_ready_refines_the_public_outcome_gate:
  assumes effect: "final_effect_key (envelope_command (payload_envelope (result_payload recorded)))
      (result_outcome recorded) = (if final then Some origin else None)"
    and publication: "(origin \<in> core_published (call_authority_state (product_calls (outcome_source state)))) =
      cg_present (cg_publication row)"
    and owner: "asset_owner (machine_state (core_parent (call_authority_state (product_calls (outcome_source state)))))
      (envelope_asset (payload_envelope (result_payload recorded))) = lock_owner"
  shows "cg_ready final origin lock_owner row = result_completion_ready recorded state"
  using effect publication owner
  by (cases final) (simp_all add: cg_gate_with_def result_completion_ready_def Let_def)

datatype 'outcome cg_reply = CG_Waiting | CG_Rejected | CG_Collected 'outcome

fun cg_collect_view where
  "cg_collect_view None = (CG_Waiting, False)"
| "cg_collect_view (Some (matches, ready, outcome)) =
     (if \<not> matches then (CG_Rejected, False)
      else if ready then (CG_Collected outcome, True) else (CG_Waiting, False))"

definition cg_observe_with where
  "cg_observe_with require_publication require_release final origin lock_owner row requested stored =
    cg_collect_view (map_option (\<lambda>(retained, outcome).
      let matches = retained = requested
      in (matches, matches \<and> cg_gate_with require_publication require_release final origin lock_owner row, outcome)) stored)"

abbreviation cg_observe where
  "cg_observe \<equiv> cg_observe_with True True"

fun cg_project_reply where
  "cg_project_reply CG_Waiting = None"
| "cg_project_reply CG_Rejected = None"
| "cg_project_reply (CG_Collected outcome) = Some outcome"

lemma cg_ordinary_observe_refines_the_public_retained_result:
  assumes access: "result_access_bound verified who call_id requested state"
    and stored: "native_stored = map_option (\<lambda>recorded. (result_payload recorded, result_outcome recorded))
      (outcome_entries state call_id)"
    and gate: "\<And>recorded. outcome_entries state call_id = Some recorded \<Longrightarrow>
      cg_ready final origin lock_owner row = result_completion_ready recorded state"
  shows "cg_project_reply (fst (cg_observe final origin lock_owner row requested native_stored)) =
      read_authoritative_result verified who call_id requested state"
  using access stored gate
  by (cases "outcome_entries state call_id")
     (auto simp: cg_observe_with_def read_authoritative_result_def Let_def split: if_splits)

definition cg_finish where
  "cg_finish call_id completed observation =
    (if snd observation then insert call_id completed else completed, fst observation)"

lemma cg_exact_ready_result_can_be_completed_once:
  "cg_finish call_id (fst (cg_finish call_id completed observation)) observation =
    cg_finish call_id completed observation"
  by (simp add: cg_finish_def)

lemma cg_missing_publication_control:
  assumes "lock_owner \<noteq> Some origin" "cg_publication row = None"
  shows "cg_observe True origin lock_owner row requested (Some (requested, outcome)) = (CG_Waiting, False)"
    and "cg_observe_with False True True origin lock_owner row requested (Some (requested, outcome)) =
      (CG_Collected outcome, True)"
  using assms by (simp_all add: cg_observe_with_def cg_gate_with_def)

lemma cg_retained_lock_control:
  assumes "cg_publication row = Some decision"
  shows "cg_observe True origin (Some origin) row requested (Some (requested, outcome)) = (CG_Waiting, False)"
    and "cg_observe_with True False True origin (Some origin) row requested (Some (requested, outcome)) =
      (CG_Collected outcome, True)"
  using assms by (simp_all add: cg_observe_with_def cg_gate_with_def)

lemma cg_payload_mismatch_precedes_the_gate:
  assumes "retained \<noteq> requested"
  shows "cg_observe_with check_publication check_release final origin lock_owner row requested
      (Some (retained, outcome)) = (CG_Rejected, False)"
  using assms by (simp add: cg_observe_with_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms cg_ready_refines_the_public_outcome_gate
    cg_ordinary_observe_refines_the_public_retained_result cg_exact_ready_result_can_be_completed_once
    cg_missing_publication_control cg_retained_lock_control cg_payload_mismatch_precedes_the_gate})
  then () else error "Unexpected oracle in retained completion gates"
\<close>

end
