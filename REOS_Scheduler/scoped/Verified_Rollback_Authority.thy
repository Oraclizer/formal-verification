theory Verified_Rollback_Authority
  imports REOS_Rollback_Examples.Rollback_Examples
begin

datatype request_origin = Direct_Request | Regulatory_Review

record verified_inputs =
  verified_origin :: "rollback_intent \<Rightarrow> request_origin option"
  collective_decisions :: "rollback_intent set"
  exact_context_updates :: "(nat \<times> nat \<times> nat \<times> nat) set"

text \<open>This entry relation consumes classifications and collective decisions
that an authority has authenticated for the exact intent. Ordinary actor
authentication and wide-scope ratification are checked by the existing
rollback transition.\<close>

definition checked_rollback ::
  "verified_inputs \<Rightarrow> rollback_state \<Rightarrow> rollback_intent \<Rightarrow> nat option \<Rightarrow>
   nat option \<Rightarrow> rollback_result \<times> rollback_state"
where
  "checked_rollback inputs s r ratification role_proof =
    (case verified_origin inputs r of None \<Rightarrow> (Rejected Unauthenticated_Intent, s)
     | Some origin \<Rightarrow>
       if (requested_role r = Governance \<or> origin = Regulatory_Review)
           \<and> r \<notin> collective_decisions inputs
       then (Rejected Approval_Required, s)
       else execute s (Execute_Rollback r ratification role_proof))"

definition checked_advance ::
  "verified_inputs \<Rightarrow> rollback_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    rollback_result \<times> rollback_state"
where
  "checked_advance inputs s time authority k policy =
    (if (time, authority, k, policy) \<in> exact_context_updates inputs
     then execute s (Advance_Context time authority k policy)
     else (Rejected Invalid_Context, s))"

lemma rejected_context_cannot_activate_future_grants:
  assumes "(time, authority, k, policy) \<notin> exact_context_updates inputs"
  shows "checked_advance inputs s time authority k policy = (Rejected Invalid_Context, s)"
  using assms by (simp add: checked_advance_def)

lemma accepted_governance_or_review_has_the_exact_decision:
  assumes run: "checked_rollback inputs s r a rp = (Accepted request, t)"
    and governance_or_review:
      "requested_role r = Governance \<or> verified_origin inputs r = Some Regulatory_Review"
  shows "r \<in> collective_decisions inputs"
  using assms by (auto simp: checked_rollback_def split: option.splits if_splits)

definition governed_intent :: rollback_intent where
  "governed_intent = intent\<lparr>requester := 1, requested_role := Governance\<rparr>"

definition unapproved :: verified_inputs where
  "unapproved = \<lparr>
     verified_origin = (\<lambda>r. if r = governed_intent then Some Direct_Request
        else if r = intent then Some Regulatory_Review else None),
     collective_decisions = {}, exact_context_updates = {}\<rparr>"

lemma collective_decision_controls_targeted_governance_and_appeal:
  "checked_rollback unapproved fixture governed_intent None None = (Rejected Approval_Required, fixture)"
  "checked_rollback unapproved fixture intent None None = (Rejected Approval_Required, fixture)"
  "checked_rollback (unapproved\<lparr>collective_decisions := {intent}\<rparr>) fixture governed_intent None None
    = (Rejected Approval_Required, fixture)"
  "\<exists>t. checked_rollback (unapproved\<lparr>collective_decisions := {governed_intent}\<rparr>)
    fixture governed_intent None None = (Accepted 11, t)"
  "\<exists>t. checked_rollback (unapproved\<lparr>collective_decisions := {intent}\<rparr>)
    fixture intent None None = (Accepted 11, t)"
  by (simp_all add: checked_rollback_def unapproved_def governed_intent_def fixture_setup decision_rules)

lemma a_matched_context_update_reaches_the_published_transition:
  "checked_advance unapproved fixture 5 4 9 9 = (Rejected Invalid_Context, fixture)"
  "\<exists>t. checked_advance (unapproved\<lparr>exact_context_updates := {(5,4,9,9)}\<rparr>)
     fixture 5 4 9 9 = (Internal Context_Advanced, t) \<and> policy_epoch t 9 = 9"
  by (simp_all add: checked_advance_def unapproved_def fixture_setup)

end
