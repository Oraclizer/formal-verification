theory Promotion_Cutover
  imports Operational_Degree
begin

record cutover_metadata =
  required_level :: operational_level
  chosen_path :: operational_level
  meter_version :: nat
  cutover_epoch :: nat

record billing_entry =
  binding_id :: nat
  billing_level :: operational_level
  billing_version :: nat
  billing_epoch :: nat
  domains_written :: nat

record 'd cutover_state =
  route_metadata :: cutover_metadata
  binding_state :: "'d flow_state"
  billing_history :: "billing_entry list"
  unreconciled_soft_write :: bool

type_synonym promotion_grants = "(nat \<times> nat) set"

datatype 'd cutover_action =
    Confirm_Promotion nat nat
  | Commit_Binding nat cutover_metadata 'd 'd nat bool

datatype cutover_ok = Promotion_Finalized | Binding_Committed
datatype cutover_error = Ineligible_Promotion | Stale_Ticket | Disallowed_Route
type_synonym cutover_result = "(cutover_ok, cutover_error, flow_failure, unit) transition_result"

definition promotion_allowed :: "promotion_grants \<Rightarrow> 'd cutover_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "promotion_allowed grants s epoch version \<longleftrightarrow>
    (epoch, version) \<in> grants \<and> cutover_epoch (route_metadata s) < epoch \<and>
    required_level (route_metadata s) = Coupled \<and> \<not> unreconciled_soft_write s"

definition promoted_metadata :: "nat \<Rightarrow> nat \<Rightarrow> cutover_metadata" where
  "promoted_metadata epoch version =
    \<lparr>required_level = Atomic, chosen_path = Atomic, meter_version = version, cutover_epoch = epoch\<rparr>"

definition billing_record :: "nat \<Rightarrow> cutover_metadata \<Rightarrow> 'd flow_action \<Rightarrow> billing_entry" where
  "billing_record i meta a =
    \<lparr>binding_id = i, billing_level = required_level meta, billing_version = meter_version meta,
      billing_epoch = cutover_epoch meta, domains_written = card (participants a)\<rparr>"

definition can_commit ::
  "'d flow_policy \<Rightarrow> 'd cutover_state \<Rightarrow> nat \<Rightarrow> cutover_metadata \<Rightarrow> 'd flow_action \<Rightarrow> bool"
where
  "can_commit p s i ticket action \<longleftrightarrow>
     ticket = route_metadata s \<and> i \<notin> set (map binding_id (billing_history s)) \<and>
     level_rank Coupled \<le> level_rank (required_level ticket) \<and>
     level_rank (required_level ticket) \<le> level_rank (chosen_path ticket) \<and>
     legal_at p (required_level ticket) action"

inductive cutover_step ::
  "'d flow_policy \<Rightarrow> promotion_grants \<Rightarrow> ('d cutover_state, 'd cutover_action, cutover_result) step_rel"
  for p grants
where
  Promote:
    "promotion_allowed grants s epoch version \<Longrightarrow>
      cutover_step p grants s (Confirm_Promotion epoch version) (Accepted Promotion_Finalized)
        (s\<lparr>route_metadata := promoted_metadata epoch version\<rparr>)"
| Refuse_Promotion:
    "\<not> promotion_allowed grants s epoch version \<Longrightarrow>
      cutover_step p grants s (Confirm_Promotion epoch version) (Rejected Ineligible_Promotion) s"
| Commit:
    "\<lbrakk>a = Commit_From origin destination value; can_commit p s i ticket a;
      flow_step p (chosen_path ticket) healthy (binding_state s) a (Accepted (Committed_Value value)) t\<rbrakk> \<Longrightarrow>
      cutover_step p grants s (Commit_Binding i ticket origin destination value healthy) (Accepted Binding_Committed)
        (s\<lparr>binding_state := t, billing_history := billing_history s @ [billing_record i ticket a]\<rparr>)"
| Binding_Failed:
    "\<lbrakk>a = Commit_From origin destination value; can_commit p s i ticket a;
      flow_step p (chosen_path ticket) healthy (binding_state s) a (Operational_Failure failure) t\<rbrakk> \<Longrightarrow>
      cutover_step p grants s (Commit_Binding i ticket origin destination value healthy) (Operational_Failure failure)
        (s\<lparr>binding_state := t, unreconciled_soft_write := unreconciled_soft_write s \<or> failure = Partial_Write\<rparr>)"
| Refuse_Stale:
    "ticket \<noteq> route_metadata s \<Longrightarrow>
      cutover_step p grants s (Commit_Binding i ticket origin destination value healthy) (Rejected Stale_Ticket) s"
| Refuse_Unroutable:
    "\<lbrakk>ticket = route_metadata s; \<not> can_commit p s i ticket (Commit_From origin destination value)\<rbrakk> \<Longrightarrow>
      cutover_step p grants s (Commit_Binding i ticket origin destination value healthy) (Rejected Disallowed_Route) s"

theorem accepted_promotion_has_one_metadata_boundary:
  assumes "cutover_step p grants s (Confirm_Promotion epoch version) (Accepted Promotion_Finalized) t"
  shows "route_metadata t = promoted_metadata epoch version \<and>
    binding_state t = binding_state s \<and> billing_history t = billing_history s \<and>
    required_level (route_metadata s) = Coupled \<and> \<not> unreconciled_soft_write s"
  using assms by (cases rule: cutover_step.cases) (auto simp: promotion_allowed_def)

lemma unsafe_soft_effect_blocks_promotion:
  assumes "unreconciled_soft_write s"
  shows "cutover_step p grants s (Confirm_Promotion epoch version) (Rejected Ineligible_Promotion) s \<and>
    (\<not> (\<exists>t. cutover_step p grants s (Confirm_Promotion epoch version) (Accepted Promotion_Finalized) t))"
  using assms by (auto intro: cutover_step.Refuse_Promotion
    elim: cutover_step.cases simp: promotion_allowed_def)

lemma stale_ticket_cannot_commit_after_promotion:
  assumes promote: "cutover_step p grants s (Confirm_Promotion epoch version) (Accepted Promotion_Finalized) t"
    and old: "ticket = route_metadata s"
    and attempt: "cutover_step p grants t (Commit_Binding i ticket origin dst value healthy) result u"
  shows "result = Rejected Stale_Ticket \<and> u = t"
proof -
  have "ticket \<noteq> route_metadata t"
    using accepted_promotion_has_one_metadata_boundary[OF promote] old
    by (metis operational_level.distinct(11) promoted_metadata_def cutover_metadata.select_convs(1))
  with attempt show ?thesis
    using attempt by (cases rule: cutover_step.cases) (auto simp: can_commit_def)
qed

lemma commit_adds_one_required_level_bill:
  assumes "cutover_step p grants s (Commit_Binding i ticket origin dst value healthy) (Accepted Binding_Committed) t"
  shows "ticket = route_metadata s \<and> route_metadata t = route_metadata s \<and>
    billing_history t = billing_history s @ [billing_record i (route_metadata s) (Commit_From origin dst value)] \<and>
    committed (binding_state t) origin = value \<and> committed (binding_state t) dst = value"
  using assms
  by (cases rule: cutover_step.cases) (auto simp: flow_step_def can_commit_def split: if_splits)

lemma commit_failure_keeps_billing_history:
  assumes "cutover_step p grants s a (Operational_Failure failure) t"
  shows "billing_history t = billing_history s"
  using assms by (cases rule: cutover_step.cases) auto

end
