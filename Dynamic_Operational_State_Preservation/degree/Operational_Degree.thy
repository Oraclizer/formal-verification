theory Operational_Degree
  imports Operational_Trace_Contracts.Operational_Trace_Contracts
begin

datatype operational_level = Static | Observation | Coupled | Atomic

fun level_rank :: "operational_level \<Rightarrow> nat" where
  "level_rank Static = 0"
| "level_rank Observation = 1"
| "level_rank Coupled = 2"
| "level_rank Atomic = 3"

record 'd flow_policy =
  hub :: 'd
  domain_set :: "'d set"
  allowed_sources :: "'d set"

datatype 'd flow_action = Read_From 'd 'd | Commit_From 'd 'd nat
datatype flow_success = Read_Value nat | Committed_Value nat
datatype flow_failure = Partial_Write | Rolled_Back

type_synonym flow_result = "(flow_success, unit, flow_failure, unit) transition_result"

record 'd flow_state =
  committed :: "'d \<Rightarrow> nat"
  observation_cache :: "'d \<Rightarrow> nat"

fun participants :: "'d flow_action \<Rightarrow> 'd set" where
  "participants (Read_From origin receiver) = {origin, receiver}"
| "participants (Commit_From origin receiver value) = {origin, receiver}"

fun legal_at :: "'d flow_policy \<Rightarrow> operational_level \<Rightarrow> 'd flow_action \<Rightarrow> bool" where
  "legal_at p rank (Read_From origin receiver) \<longleftrightarrow>
     level_rank Observation \<le> level_rank rank \<and> origin = hub p \<and> {origin, receiver} \<subseteq> domain_set p"
| "legal_at p rank (Commit_From origin receiver value) \<longleftrightarrow>
     level_rank Coupled \<le> level_rank rank \<and> origin \<in> allowed_sources p \<and>
     origin \<noteq> receiver \<and> {origin, receiver} \<subseteq> domain_set p"

fun evaluate_flow ::
  "'d flow_policy \<Rightarrow> operational_level \<Rightarrow> bool \<Rightarrow>
   'd flow_state \<Rightarrow> 'd flow_action \<Rightarrow> 'd flow_state \<times> flow_result"
where
  "evaluate_flow p rank receiver_healthy s (Read_From origin receiver) =
    (if legal_at p rank (Read_From origin receiver)
     then (s\<lparr>observation_cache := (observation_cache s)(receiver := committed s origin)\<rparr>,
           Accepted (Read_Value (committed s origin)))
     else (s, Rejected ()))"
| "evaluate_flow p rank receiver_healthy s (Commit_From origin receiver value) =
    (if \<not> legal_at p rank (Commit_From origin receiver value) then (s, Rejected ())
     else if receiver_healthy then
       (s\<lparr>committed := ((committed s)(origin := value))(receiver := value)\<rparr>,
        Accepted (Committed_Value value))
     else if rank = Atomic then (s, Operational_Failure Rolled_Back)
     else (s\<lparr>committed := (committed s)(origin := value)\<rparr>, Operational_Failure Partial_Write))"

definition flow_step ::
  "'d flow_policy \<Rightarrow> operational_level \<Rightarrow> bool \<Rightarrow> ('d flow_state, 'd flow_action, flow_result) step_rel"
where
  "flow_step p rank receiver_healthy s a r t \<longleftrightarrow>
     evaluate_flow p rank receiver_healthy s a = (t, r)"

definition successful_actions :: "'d flow_policy \<Rightarrow> operational_level \<Rightarrow> 'd flow_action set" where
  "successful_actions p rank = {a. \<exists>s t value. flow_step p rank True s a (Accepted value) t}"

lemma successful_actions_are_legal:
  "a \<in> successful_actions p rank \<longleftrightarrow> legal_at p rank a"
  by (cases a) (auto simp: successful_actions_def flow_step_def split: if_splits)

theorem nonhub_coupling_strictly_extends_observation:
  assumes "origin \<noteq> hub p" "origin \<in> allowed_sources p"
    "origin \<noteq> receiver" "origin \<in> domain_set p" "receiver \<in> domain_set p"
  shows "successful_actions p Observation \<subset> successful_actions p Coupled \<and>
    (\<exists>t. flow_step p Coupled True s (Commit_From origin receiver value)
       (Accepted (Committed_Value value)) t \<and> committed t origin = value \<and> committed t receiver = value) \<and>
    flow_step p Observation True s (Commit_From origin receiver value) (Rejected ()) s"
proof -
  have incl: "successful_actions p Observation \<subseteq> successful_actions p Coupled"
    by (auto simp: successful_actions_are_legal; rename_tac request; case_tac request; simp)
  have gap: "Commit_From origin receiver value \<in> successful_actions p Coupled -
       successful_actions p Observation"
    using assms by (simp add: successful_actions_are_legal)
  have writes: "\<exists>t. flow_step p Coupled True s (Commit_From origin receiver value)
       (Accepted (Committed_Value value)) t \<and> committed t origin = value \<and> committed t receiver = value"
    using assms by (auto simp: flow_step_def)
  show ?thesis using incl gap writes by (auto simp: flow_step_def)
qed

lemma independent_initiators_have_distinct_paths:
  assumes "a \<in> allowed_sources p" "b \<in> allowed_sources p" "a \<noteq> b"
    "a \<noteq> d" "b \<noteq> d" "{a,b,d} \<subseteq> domain_set p"
  shows "{Commit_From a d v, Commit_From b d v} \<subseteq> successful_actions p Coupled \<and>
     Commit_From a d v \<noteq> Commit_From b d v"
  using assms by (auto simp: successful_actions_are_legal)

definition restrict_policy :: "'d set \<Rightarrow> 'd flow_policy \<Rightarrow> 'd flow_policy" where
  "restrict_policy keep p =
    p\<lparr>domain_set := domain_set p \<inter> keep, allowed_sources := allowed_sources p \<inter> keep\<rparr>"

definition forget_outside :: "'d set \<Rightarrow> 'd flow_state \<Rightarrow> 'd flow_state" where
  "forget_outside keep s =
    \<lparr>committed = (\<lambda>d. if d \<in> keep then committed s d else 0),
      observation_cache = (\<lambda>d. if d \<in> keep then observation_cache s d else 0)\<rparr>"

lemma forget_composes:
  "forget_outside first (forget_outside second s) = forget_outside (first \<inter> second) s"
  by (simp add: forget_outside_def fun_eq_iff)

lemma forget_observation_update:
  assumes "origin \<in> keep" "destination \<in> keep"
  shows "forget_outside keep (s\<lparr>observation_cache := (observation_cache s)(destination := committed s origin)\<rparr>) =
    (forget_outside keep s)\<lparr>observation_cache :=
      (observation_cache (forget_outside keep s))(destination := committed (forget_outside keep s) origin)\<rparr>"
  using assms by (simp add: forget_outside_def fun_eq_iff)

lemma forget_commit_update:
  assumes "d \<in> keep"
  shows "forget_outside keep (s\<lparr>committed := (committed s)(d := v)\<rparr>) =
    (forget_outside keep s)\<lparr>committed := (committed (forget_outside keep s))(d := v)\<rparr>"
  using assms by (simp add: forget_outside_def fun_eq_iff)

lemma forget_two_commit_updates:
  assumes "origin \<in> keep" "destination \<in> keep"
  shows "forget_outside keep
     (s\<lparr>committed := (committed s)(origin := v, destination := v)\<rparr>) =
    (forget_outside keep s)\<lparr>committed :=
      (committed (forget_outside keep s))(origin := v, destination := v)\<rparr>"
  using assms by (simp add: forget_outside_def fun_eq_iff fun_upd_apply)

lemma flow_naturality_in_scope:
  assumes "participants a \<subseteq> keep" "flow_step p rank healthy s a r t"
  shows "flow_step (restrict_policy keep p) rank healthy (forget_outside keep s) a r (forget_outside keep t)"
proof -
  have guard: "legal_at (restrict_policy keep p) rank a = legal_at p rank a"
    using assms(1) by (cases a) (auto simp: restrict_policy_def)
  have evaluate: "evaluate_flow (restrict_policy keep p) rank healthy (forget_outside keep s) a =
    map_prod (forget_outside keep) id (evaluate_flow p rank healthy s a)"
  proof (cases a)
    case (Read_From origin destination)
    with assms(1) have keep: "origin \<in> keep" "destination \<in> keep" by auto
    have read_guard: "legal_at (restrict_policy keep p) rank (Read_From origin destination) =
      legal_at p rank (Read_From origin destination)"
      using guard by (simp only: Read_From)
    have origin_value: "committed (forget_outside keep s) origin = committed s origin"
      using keep by (simp add: forget_outside_def)
    have cache: "(forget_outside keep s)\<lparr>observation_cache :=
        (observation_cache (forget_outside keep s))(destination := committed s origin)\<rparr> =
      forget_outside keep (s\<lparr>observation_cache := (observation_cache s)(destination := committed s origin)\<rparr>)"
      using forget_observation_update[OF keep, of s] by (simp only: origin_value)
    show ?thesis unfolding Read_From evaluate_flow.simps read_guard
      by (cases "legal_at p rank (Read_From origin destination)")
         (simp_all only: if_True if_False map_prod_simp id_apply origin_value cache)
  next
    case (Commit_From origin destination v)
    with assms(1) have keep: "origin \<in> keep" "destination \<in> keep" by auto
    have commit_guard: "legal_at (restrict_policy keep p) rank (Commit_From origin destination v) =
      legal_at p rank (Commit_From origin destination v)"
      using guard by (simp only: Commit_From)
    show ?thesis unfolding Commit_From evaluate_flow.simps commit_guard
      by (simp add: forget_commit_update forget_two_commit_updates keep split: if_splits)
  qed
  show ?thesis using evaluate assms(2) by (simp add: flow_step_def)
qed

lemma erasing_a_source_can_lose_a_successful_action:
  assumes "origin \<in> domain_set p" "receiver \<in> domain_set p"
    "origin \<in> allowed_sources p" "origin \<noteq> receiver" "origin \<notin> keep"
  shows "Commit_From origin receiver value \<in> successful_actions p Coupled \<and>
    Commit_From origin receiver value \<notin> successful_actions (restrict_policy keep p) Coupled"
  using assms by (simp add: successful_actions_are_legal restrict_policy_def)

lemma oversupply_preserves_successful_execution:
  assumes "level_rank required \<le> level_rank supplied"
    "flow_step p required True s a (Accepted outcome) t"
  shows "flow_step p supplied True s a (Accepted outcome) t"
  using assms by (cases a) (auto simp: flow_step_def split: if_splits)

lemma undersupply_can_change_a_committed_cell_on_failure:
  assumes "legal_at p Coupled (Commit_From origin receiver value)" "value \<noteq> committed s origin"
  shows "flow_step p Atomic False s (Commit_From origin receiver value) (Operational_Failure Rolled_Back) s \<and>
    (\<exists>t. flow_step p Coupled False s (Commit_From origin receiver value) (Operational_Failure Partial_Write) t \<and>
      committed t origin \<noteq> committed s origin \<and> committed t receiver = committed s receiver)"
  using assms by (auto simp: flow_step_def)

lemma oversupply_does_not_preserve_partial_failure:
  assumes "legal_at p Coupled (Commit_From origin receiver value)"
  shows "\<not> (\<exists>t. flow_step p Atomic False s (Commit_From origin receiver value) (Operational_Failure Partial_Write) t)"
  using assms by (simp add: flow_step_def)

end
