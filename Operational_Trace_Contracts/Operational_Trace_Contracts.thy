theory Operational_Trace_Contracts
  imports Main
begin

datatype ('accept, 'reject, 'fault, 'internal) transition_result =
    Accepted 'accept
  | Rejected 'reject
  | Operational_Failure 'fault
  | Internal 'internal

type_synonym ('s, 'a, 'r) step_rel = "'s \<Rightarrow> 'a \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"

record ('s, 'a, 'r) transition =
  source_state :: 's
  step_action :: 'a
  step_outcome :: 'r
  target_state :: 's

definition step_occurs :: "('s, 'a, 'r) step_rel \<Rightarrow> ('s, 'a, 'r) transition \<Rightarrow> bool"
  where
    "step_occurs step e \<longleftrightarrow>
      step (source_state e) (step_action e) (step_outcome e) (target_state e)"

fun finite_trace ::
  "('s, 'a, 'r) step_rel \<Rightarrow> 's set \<Rightarrow> 's \<Rightarrow>
    ('s, 'a, 'r) transition list \<Rightarrow> 's \<Rightarrow> bool"
  where
    "finite_trace step carrier s [] t \<longleftrightarrow> s \<in> carrier \<and> s = t"
  | "finite_trace step carrier s (e # es) t \<longleftrightarrow>
      s \<in> carrier \<and> source_state e = s \<and> step_occurs step e \<and>
      finite_trace step carrier (target_state e) es t"

definition infinite_run ::
  "('s, 'a, 'r) step_rel \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow>
    (nat \<Rightarrow> ('s, 'a, 'r) transition) \<Rightarrow> bool"
  where
    "infinite_run step init carrier events \<longleftrightarrow>
      source_state (events 0) \<in> init \<and>
      (\<forall>n. source_state (events n) \<in> carrier \<and> step_occurs step (events n) \<and>
        target_state (events n) = source_state (events (Suc n)))"

type_synonym ('observer, 'policy, 's, 'a, 'r, 'view) observation =
  "'observer \<Rightarrow> 'policy \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> 'view"

definition observe_event ::
  "('observer, 'policy, 's, 'a, 'r, 'view) observation \<Rightarrow> 'observer \<Rightarrow> 'policy
    \<Rightarrow> ('s, 'a, 'r) transition \<Rightarrow> 'view"
  where
    "observe_event observe observer policy e =
      observe observer policy (source_state e) (step_action e) (step_outcome e) (target_state e)"

definition observe_trace ::
  "('observer, 'policy, 's, 'a, 'r, 'view) observation \<Rightarrow> 'observer \<Rightarrow> 'policy
    \<Rightarrow> ('s, 'a, 'r) transition list \<Rightarrow> 'view list"
  where
    "observe_trace observe observer policy = map (observe_event observe observer policy)"

definition observational_stutter ::
  "('observer \<Rightarrow> 'policy \<Rightarrow> 's \<Rightarrow> 'view) \<Rightarrow> 'observer \<Rightarrow> 'policy
    \<Rightarrow> ('s, 'a, 'r) transition \<Rightarrow> bool"
  where
    "observational_stutter view observer policy e \<longleftrightarrow>
      view observer policy (source_state e) = view observer policy (target_state e)"

definition preserves_outside ::
  "('s \<Rightarrow> 'cell \<Rightarrow> 'value) \<Rightarrow> 'cell set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  where
    "preserves_outside read footprint s t \<longleftrightarrow>
      (\<forall>cell. cell \<notin> footprint \<longrightarrow> read t cell = read s cell)"

definition update_cells ::
  "'cell set \<Rightarrow> ('cell \<Rightarrow> 'value) \<Rightarrow> ('cell \<Rightarrow> 'value) \<Rightarrow> 'cell \<Rightarrow> 'value"
  where
    "update_cells footprint replacement old cell =
      (if cell \<in> footprint then replacement cell else old cell)"

lemma update_cells_frame:
  "preserves_outside id footprint old (update_cells footprint replacement old)"
  by (simp add: preserves_outside_def update_cells_def)

definition rank_decreases :: "('s \<Rightarrow> nat) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  where "rank_decreases rank s t \<longleftrightarrow> rank t < rank s"

definition rank_nonincreasing :: "('s \<Rightarrow> nat) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  where "rank_nonincreasing rank s t \<longleftrightarrow> rank t \<le> rank s"

lemma wf_rank_decreases:
  "wf {(t, s). rank_decreases rank s t}"
proof -
  have "{(t, s). rank_decreases rank s t} = measure rank"
    by (auto simp: rank_decreases_def measure_def)
  then show ?thesis by simp
qed

end
