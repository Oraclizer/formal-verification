(* SPDX-License-Identifier: BSD-3-Clause *)
theory Funding_Realization
  imports "Evidence_Atomic_Binding.Funding_Decision_Information"
begin

section \<open>Constructive Words of Actual Descendant Operations\<close>

definition realization_effect :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> descendant_effect" where
  "realization_effect root sender recipient amount =
    \<lparr>lineage_root=root,lineage_from=sender,lineage_to=recipient,lineage_amount=amount,
      lineage_operation=Ordinary_Transfer_Effect,lineage_caller=0,
      lineage_authority_epoch=0,lineage_version=0\<rparr>"

definition realization_action :: "source_certificate \<Rightarrow> descendant_effect \<Rightarrow> reservation_action" where
  "realization_action certificate e = Descendant_Action
    (funding_probe_context (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e))
    (funding_probe_request certificate (lineage_root e) (lineage_to e) (lineage_amount e))
    (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)"

definition realization_actions :: "(transfer_binding \<Rightarrow> source_certificate) \<Rightarrow>
  descendant_effect list \<Rightarrow> reservation_action list" where
  "realization_actions certificates effects =
    map (\<lambda>e. realization_action (certificates (lineage_root e)) e) effects"

definition realization_result :: "(transfer_binding \<Rightarrow> source_certificate) \<Rightarrow>
  descendant_effect \<Rightarrow> reservation_machine \<Rightarrow> reservation_machine \<times> reservation_reply" where
  "realization_result certificates e m = execute_descendant
    (funding_probe_context (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e))
    (funding_probe_request (certificates (lineage_root e)) (lineage_root e) (lineage_to e) (lineage_amount e))
    (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e) m"

fun run_realization :: "(transfer_binding \<Rightarrow> source_certificate) \<Rightarrow>
  descendant_effect list \<Rightarrow> reservation_machine \<Rightarrow> reservation_machine" where
  "run_realization certificates [] m=m"
| "run_realization certificates (e#effects) m =
    run_realization certificates effects (fst (realization_result certificates e m))"

fun realization_succeeds :: "(transfer_binding \<Rightarrow> source_certificate) \<Rightarrow>
  descendant_effect list \<Rightarrow> reservation_machine \<Rightarrow> bool" where
  "realization_succeeds certificates [] m=True"
| "realization_succeeds certificates (e#effects) m =
    (snd (realization_result certificates e m)=Descendant_Executed \<and>
      realization_succeeds certificates effects (fst (realization_result certificates e m)))"

definition realization_units :: "reservation_machine \<Rightarrow> transfer_binding \<Rightarrow> nat \<Rightarrow> nat" where
  "realization_units m root holder =
    funded_units (machine_state m) (binding_key root,holder_account root holder)"

definition realization_move :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  descendant_effect list" where
  "realization_move root sender recipient amount =
    (if amount=0 then [] else [realization_effect root sender recipient amount])"

definition realization_drain :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> descendant_effect list" where
  "realization_drain root anchor holders values =
    concat (map (\<lambda>h. realization_move root h anchor (values h)) holders)"

definition realization_distribute :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> descendant_effect list" where
  "realization_distribute root anchor holders target =
    concat (map (\<lambda>h. realization_move root anchor h (target h)) holders)"

fun realization_row :: "transfer_binding \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> descendant_effect list" where
  "realization_row root [] values target=[]"
| "realization_row root (anchor#holders) values target =
    realization_drain root anchor holders values @ realization_distribute root anchor holders target"

definition realization_plan_from :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow>
  (transfer_binding \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (transfer_binding \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
  descendant_effect list" where
  "realization_plan_from roots holders values target =
    concat (map (\<lambda>root. realization_row root holders (values root) (target root)) roots)"

definition realization_plan :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow> reservation_machine \<Rightarrow>
  (transfer_binding \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> descendant_effect list" where
  "realization_plan roots holders m target =
    realization_plan_from roots holders (realization_units m) target"

definition canonical_realization_effect :: "descendant_effect \<Rightarrow> bool" where
  "canonical_realization_effect e \<longleftrightarrow>
    e=realization_effect (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)"

lemma realization_effect_canonical [simp]:
  "canonical_realization_effect (realization_effect root sender recipient amount)"
  by (simp add: canonical_realization_effect_def realization_effect_def)

lemma run_realization_append:
  "run_realization certificates (first@second) m =
    run_realization certificates second (run_realization certificates first m)"
  by (induction first arbitrary:m) simp_all

lemma realization_succeeds_append:
  "realization_succeeds certificates (first@second) m \<longleftrightarrow>
    realization_succeeds certificates first m \<and>
    realization_succeeds certificates second (run_realization certificates first m)"
  by (induction first arbitrary:m) simp_all

lemma realization_success_at_every_prefix:
  assumes "realization_succeeds certificates effects m" "i<length effects"
  shows "snd (realization_result certificates (effects!i)
    (run_realization certificates (take i effects) m))=Descendant_Executed"
  using assms
proof (induction effects arbitrary:m i)
  case Nil
  then show ?case by simp
next
  case (Cons e effects)
  then show ?case by (cases i) auto
qed

lemma realization_result_commits:
  assumes success: "snd (realization_result certificates e m)=Descendant_Executed"
  shows "fst (realization_result certificates e m) =
    fst (record_observation
      (funding_probe_request (certificates (lineage_root e)) (lineage_root e) (lineage_to e) (lineage_amount e))
      Descendant_Executed (commit_reservation_event (Descendant_Event
        (realization_effect (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e))) m))"
  using success
  by (auto simp: realization_result_def execute_descendant_def funding_probe_request_def
      descendant_binding_def realization_effect_def record_observation_def Let_def split: if_splits)

lemma realization_result_credit [simp]:
  "received_messages (machine_state (fst (realization_result certificates e m))) =
    received_messages (machine_state m)"
  by (auto simp: realization_result_def execute_descendant_def record_observation_def
      commit_reservation_event_def Let_def split: if_splits)

lemma run_realization_credit [simp]:
  "received_messages (machine_state (run_realization certificates effects m)) =
    received_messages (machine_state m)"
  by (induction effects arbitrary:m) simp_all

lemma realization_result_funding_frame:
  assumes separate: "key\<noteq>binding_key (lineage_root e) \<or>
    (account\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
      account\<noteq>holder_account (lineage_root e) (lineage_to e))"
  shows "funded_units (machine_state (fst (realization_result certificates e m))) (key,account) =
    funded_units (machine_state m) (key,account)"
  using separate
  by (auto simp: realization_result_def execute_descendant_def record_observation_def
      commit_reservation_event_def Let_def)

lemma run_realization_funding_frame:
  assumes separate: "\<forall>e\<in>set effects. key\<noteq>binding_key (lineage_root e) \<or>
    (account\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
      account\<noteq>holder_account (lineage_root e) (lineage_to e))"
  shows "funded_units (machine_state (run_realization certificates effects m)) (key,account) =
    funded_units (machine_state m) (key,account)"
  using separate
proof (induction effects arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons e effects)
  have head: "funded_units (machine_state (fst (realization_result certificates e m))) (key,account) =
      funded_units (machine_state m) (key,account)"
    by (rule realization_result_funding_frame) (use Cons.prems in simp)
  have tail: "funded_units (machine_state (run_realization certificates effects
      (fst (realization_result certificates e m)))) (key,account) =
      funded_units (machine_state (fst (realization_result certificates e m))) (key,account)"
    by (rule Cons.IH) (use Cons.prems in simp)
  show ?case using head tail by simp
qed

lemma realization_result_financial:
  assumes financial: "financial_history_agreement balances m"
    and success: "snd (realization_result certificates e m)=Descendant_Executed"
  shows "financial_history_agreement balances (fst (realization_result certificates e m))"
proof -
  let ?effect = "realization_effect (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)"
  have pooled: "lineage_amount e\<le>destination_units (machine_state m)
      (holder_account (lineage_root e) (lineage_from e))"
    and rooted: "lineage_amount e\<le>funded_units (machine_state m)
      (binding_key (lineage_root e),holder_account (lineage_root e) (lineage_from e))"
    using success by (auto simp: realization_result_def execute_descendant_def
        record_observation_def Let_def split: if_splits)
  have event: "financial_history_agreement balances (commit_reservation_event (Descendant_Event ?effect) m)"
    by (rule descendant_accounting_step[OF financial])
       (use pooled rooted in \<open>simp_all add: realization_effect_def\<close>)
  show ?thesis using event
    by (simp only: realization_result_commits[OF success] observation_preserves_financial_history)
qed

lemma run_realization_financial:
  assumes "financial_history_agreement balances m" "realization_succeeds certificates effects m"
  shows "financial_history_agreement balances (run_realization certificates effects m)"
  using assms
proof (induction effects arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons e effects)
  have first: "financial_history_agreement balances (fst (realization_result certificates e m))"
    by (rule realization_result_financial[OF Cons.prems(1)]) (use Cons.prems(2) in simp)
  show ?case by (simp only: run_realization.simps, rule Cons.IH[OF first])
    (use Cons.prems(2) in simp)
qed

lemma realization_move_member:
  "e\<in>set (realization_move root sender recipient amount) \<longleftrightarrow>
    0<amount \<and> e=realization_effect root sender recipient amount"
  by (auto simp: realization_move_def)

lemma realization_drain_member:
  "e\<in>set (realization_drain root anchor holders values) \<longleftrightarrow>
    (\<exists>h\<in>set holders. 0<values h \<and> e=realization_effect root h anchor (values h))"
  by (auto simp: realization_drain_def realization_move_member)

lemma realization_distribute_member:
  "e\<in>set (realization_distribute root anchor holders target) \<longleftrightarrow>
    (\<exists>h\<in>set holders. 0<target h \<and> e=realization_effect root anchor h (target h))"
  by (auto simp: realization_distribute_def realization_move_member)

lemma realization_row_support:
  assumes "e\<in>set (realization_row root holders values target)"
  shows "lineage_root e=root \<and> lineage_from e\<in>set holders \<and> lineage_to e\<in>set holders \<and>
    0<lineage_amount e \<and> canonical_realization_effect e"
  using assms by (cases holders)
    (auto simp: realization_drain_member realization_distribute_member realization_effect_def
      canonical_realization_effect_def)

lemma realization_plan_support:
  assumes "e\<in>set (realization_plan_from roots holders values target)"
  shows "lineage_root e\<in>set roots \<and> lineage_from e\<in>set holders \<and>
    lineage_to e\<in>set holders \<and> 0<lineage_amount e \<and> canonical_realization_effect e"
proof -
  obtain root where root: "root\<in>set roots"
    and member: "e\<in>set (realization_row root holders (values root) (target root))"
    using assms unfolding realization_plan_from_def by auto
  show ?thesis using root realization_row_support[OF member] by blast
qed

lemma realization_move_succeeds:
  assumes financial: "financial_history_agreement balances m"
    and credited: "root\<in>set (credit_history (received_messages (machine_state m)))"
    and enough: "amount\<le>realization_units m root sender"
  shows "realization_succeeds certificates (realization_move root sender recipient amount) m"
proof (cases "amount=0")
  case True
  then show ?thesis by (simp add: realization_move_def)
next
  case False
  have reply: "snd (realization_result certificates (realization_effect root sender recipient amount) m)=Descendant_Executed"
    using actual_probe_reply_is_the_funding_threshold[OF financial credited,
      where sender=sender and recipient=recipient and amount=amount and certificate="certificates root"]
      enough False
    by (simp add: realization_result_def realization_effect_def realization_units_def)
  show ?thesis using reply False by (simp add: realization_move_def)
qed

lemma realization_move_funding:
  assumes financial: "financial_history_agreement balances m"
    and credited: "root\<in>set (credit_history (received_messages (machine_state m)))"
    and enough: "amount\<le>realization_units m root sender"
    and different: "sender\<noteq>recipient"
  shows "realization_units (run_realization certificates (realization_move root sender recipient amount) m) root h =
    (if h=sender then realization_units m root sender-amount
     else if h=recipient then realization_units m root recipient+amount else realization_units m root h)"
proof (cases "amount=0")
  case True
  then show ?thesis by (simp add: realization_move_def)
next
  case False
  have success: "snd (realization_result certificates (realization_effect root sender recipient amount) m)=Descendant_Executed"
    using realization_move_succeeds[OF financial credited enough, where certificates=certificates and recipient=recipient]
      False by (simp add: realization_move_def)
  have move: "run_realization certificates (realization_move root sender recipient amount) m=
      fst (realization_result certificates (realization_effect root sender recipient amount) m)"
    using False by (simp add: realization_move_def)
  show ?thesis
    using different
    by (simp only: move realization_units_def realization_result_commits[OF success];
      auto simp: record_observation_def commit_reservation_event_def realization_effect_def
        holder_account_def Let_def split: if_splits)
qed

lemma realization_move_financial:
  assumes "financial_history_agreement balances m"
    "root\<in>set (credit_history (received_messages (machine_state m)))"
    "amount\<le>realization_units m root sender"
  shows "financial_history_agreement balances
    (run_realization certificates (realization_move root sender recipient amount) m)"
  by (rule run_realization_financial[OF assms(1)], rule realization_move_succeeds[OF assms])

section \<open>Two Structural Inductions for One Funding Row\<close>

lemma realization_drain_realizes_anchor:
  assumes financial: "financial_history_agreement balances m"
    and credited: "root\<in>set (credit_history (received_messages (machine_state m)))"
    and unique: "distinct (anchor#holders)"
    and initial_values: "\<forall>h\<in>set holders. realization_units m root h=values h"
  shows "realization_succeeds certificates (realization_drain root anchor holders values) m \<and>
    realization_units (run_realization certificates (realization_drain root anchor holders values) m) root anchor =
      realization_units m root anchor+sum_list (map values holders) \<and>
    (\<forall>h\<in>set holders. realization_units
      (run_realization certificates (realization_drain root anchor holders values) m) root h=0)"
  using assms
proof (induction holders arbitrary:m)
  case Nil
  then show ?case by (simp add: realization_drain_def)
next
  case (Cons h holders)
  let ?first = "realization_move root h anchor (values h)"
  let ?next = "run_realization certificates ?first m"
  let ?rest = "realization_drain root anchor holders values"
  have head_value: "realization_units m root h=values h" using Cons.prems(4) by simp
  have enough: "values h\<le>realization_units m root h" by (simp add: head_value)
  have different: "h\<noteq>anchor" using Cons.prems(3) by auto
  have tail_unique: "distinct (anchor#holders)" using Cons.prems(3) by simp
  have first_success: "realization_succeeds certificates ?first m"
    by (rule realization_move_succeeds[OF Cons.prems(1,2) enough])
  have next_financial: "financial_history_agreement balances ?next"
    by (rule realization_move_financial[OF Cons.prems(1,2) enough])
  have next_credit: "root\<in>set (credit_history (received_messages (machine_state ?next)))"
    using Cons.prems(2) by simp
  note change = realization_move_funding[OF Cons.prems(1,2) enough different, where certificates=certificates]
  have next_anchor: "realization_units ?next root anchor=realization_units m root anchor+values h"
    using different by (simp add: change)
  have next_head: "realization_units ?next root h=0"
    by (simp add: change head_value)
  have next_values: "\<forall>x\<in>set holders. realization_units ?next root x=values x"
  proof (intro ballI)
    fix x assume member: "x\<in>set holders"
    have "x\<noteq>h" "x\<noteq>anchor" using Cons.prems(3) member by auto
    then show "realization_units ?next root x=values x"
      using Cons.prems(4) member by (simp add: change)
  qed
  have tail: "realization_succeeds certificates ?rest ?next \<and>
    realization_units (run_realization certificates ?rest ?next) root anchor =
      realization_units ?next root anchor+sum_list (map values holders) \<and>
    (\<forall>x\<in>set holders. realization_units (run_realization certificates ?rest ?next) root x=0)"
    by (rule Cons.IH[OF next_financial next_credit tail_unique next_values])
  have head_frame: "realization_units (run_realization certificates ?rest ?next) root h=
      realization_units ?next root h"
    unfolding realization_units_def
  proof (rule run_realization_funding_frame)
    show "\<forall>e\<in>set ?rest. binding_key root\<noteq>binding_key (lineage_root e) \<or>
      (holder_account root h\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
       holder_account root h\<noteq>holder_account (lineage_root e) (lineage_to e))"
      using Cons.prems(3)
      by (auto simp: realization_drain_member realization_effect_def holder_account_def)
  qed
  have word: "realization_drain root anchor (h#holders) values=?first@?rest"
    by (simp add: realization_drain_def)
  show ?case
    using tail first_success next_anchor next_head head_frame
    by (simp add: word realization_succeeds_append run_realization_append add.assoc)
qed

lemma realization_distribute_realizes_targets:
  assumes financial: "financial_history_agreement balances m"
    and credited: "root\<in>set (credit_history (received_messages (machine_state m)))"
    and unique: "distinct (anchor#holders)"
    and empty: "\<forall>h\<in>set holders. realization_units m root h=0"
    and mass: "realization_units m root anchor=reserve+sum_list (map target holders)"
  shows "realization_succeeds certificates (realization_distribute root anchor holders target) m \<and>
    realization_units (run_realization certificates (realization_distribute root anchor holders target) m) root anchor=reserve \<and>
    (\<forall>h\<in>set holders. realization_units
      (run_realization certificates (realization_distribute root anchor holders target) m) root h=target h)"
  using assms
proof (induction holders arbitrary:m)
  case Nil
  then show ?case by (simp add: realization_distribute_def)
next
  case (Cons h holders)
  let ?first = "realization_move root anchor h (target h)"
  let ?next = "run_realization certificates ?first m"
  let ?rest = "realization_distribute root anchor holders target"
  have head_empty: "realization_units m root h=0" using Cons.prems(4) by simp
  have enough: "target h\<le>realization_units m root anchor"
    using Cons.prems(5) by simp
  have different: "anchor\<noteq>h" using Cons.prems(3) by simp
  have tail_unique: "distinct (anchor#holders)" using Cons.prems(3) by simp
  have first_success: "realization_succeeds certificates ?first m"
    by (rule realization_move_succeeds[OF Cons.prems(1,2) enough])
  have next_financial: "financial_history_agreement balances ?next"
    by (rule realization_move_financial[OF Cons.prems(1,2) enough])
  have next_credit: "root\<in>set (credit_history (received_messages (machine_state ?next)))"
    using Cons.prems(2) by simp
  note change = realization_move_funding[OF Cons.prems(1,2) enough different, where certificates=certificates]
  have next_mass: "realization_units ?next root anchor=reserve+sum_list (map target holders)"
    using Cons.prems(5) by (simp add: change add.assoc add.commute add.left_commute)
  have next_head: "realization_units ?next root h=target h"
    using different by (simp add: change head_empty)
  have next_empty: "\<forall>x\<in>set holders. realization_units ?next root x=0"
  proof (intro ballI)
    fix x assume member: "x\<in>set holders"
    have "x\<noteq>anchor" "x\<noteq>h" using Cons.prems(3) member by auto
    then show "realization_units ?next root x=0"
      using Cons.prems(4) member by (simp add: change)
  qed
  have tail: "realization_succeeds certificates ?rest ?next \<and>
    realization_units (run_realization certificates ?rest ?next) root anchor=reserve \<and>
    (\<forall>x\<in>set holders. realization_units (run_realization certificates ?rest ?next) root x=target x)"
    by (rule Cons.IH[OF next_financial next_credit tail_unique next_empty next_mass])
  have head_frame: "realization_units (run_realization certificates ?rest ?next) root h=
      realization_units ?next root h"
    unfolding realization_units_def
  proof (rule run_realization_funding_frame)
    show "\<forall>e\<in>set ?rest. binding_key root\<noteq>binding_key (lineage_root e) \<or>
      (holder_account root h\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
       holder_account root h\<noteq>holder_account (lineage_root e) (lineage_to e))"
      using Cons.prems(3)
      by (auto simp: realization_distribute_member realization_effect_def holder_account_def)
  qed
  have word: "realization_distribute root anchor (h#holders) target=?first@?rest"
    by (simp add: realization_distribute_def)
  show ?case using tail first_success next_head head_frame
    by (simp add: word realization_succeeds_append run_realization_append)
qed

theorem realization_row_is_constructive:
  assumes financial: "financial_history_agreement balances m"
    and credited: "root\<in>set (credit_history (received_messages (machine_state m)))"
    and unique: "distinct holders"
    and initial: "\<forall>h\<in>set holders. realization_units m root h=values h"
    and mass: "sum_list (map target holders)=sum_list (map values holders)"
  shows "realization_succeeds certificates (realization_row root holders values target) m \<and>
    (\<forall>h\<in>set holders. realization_units
      (run_realization certificates (realization_row root holders values target) m) root h=target h)"
proof (cases holders)
  case Nil
  then show ?thesis by simp
next
  case (Cons anchor rest)
  let ?drain = "realization_drain root anchor rest values"
  let ?middle = "run_realization certificates ?drain m"
  let ?distribute = "realization_distribute root anchor rest target"
  have tail_values: "\<forall>h\<in>set rest. realization_units m root h=values h"
    using initial by (simp add: Cons)
  have distinct: "distinct (anchor#rest)" using unique by (simp add: Cons)
  have drained: "realization_succeeds certificates ?drain m \<and>
    realization_units ?middle root anchor=realization_units m root anchor+sum_list (map values rest) \<and>
    (\<forall>h\<in>set rest. realization_units ?middle root h=0)"
    by (rule realization_drain_realizes_anchor[OF financial credited distinct tail_values])
  have middle_financial: "financial_history_agreement balances ?middle"
    by (rule run_realization_financial[OF financial]) (use drained in blast)
  have middle_credit: "root\<in>set (credit_history (received_messages (machine_state ?middle)))"
    using credited by simp
  have middle_mass: "realization_units ?middle root anchor=target anchor+sum_list (map target rest)"
    using drained initial mass by (simp add: Cons)
  have middle_empty: "\<forall>h\<in>set rest. realization_units ?middle root h=0"
    using drained by blast
  have distributed: "realization_succeeds certificates ?distribute ?middle \<and>
    realization_units (run_realization certificates ?distribute ?middle) root anchor=target anchor \<and>
    (\<forall>h\<in>set rest. realization_units (run_realization certificates ?distribute ?middle) root h=target h)"
    by (rule realization_distribute_realizes_targets
      [OF middle_financial middle_credit distinct middle_empty middle_mass])
  show ?thesis using drained distributed
    by (simp add: Cons realization_succeeds_append run_realization_append)
qed

lemma realization_plan_from_Cons:
  "realization_plan_from (root#roots) holders values target =
    realization_row root holders (values root) (target root) @
      realization_plan_from roots holders values target"
  by (simp add: realization_plan_from_def)

theorem realization_plan_from_is_constructive:
  assumes financial: "financial_history_agreement balances m"
    and credited: "\<forall>root\<in>set roots. root\<in>set (credit_history (received_messages (machine_state m)))"
    and keys: "distinct (map binding_key roots)"
    and holders: "distinct holders"
    and initial: "\<forall>root\<in>set roots. \<forall>h\<in>set holders. realization_units m root h=values root h"
    and masses: "\<forall>root\<in>set roots. sum_list (map (target root) holders)=sum_list (map (values root) holders)"
  shows "realization_succeeds certificates (realization_plan_from roots holders values target) m \<and>
    (\<forall>root\<in>set roots. \<forall>h\<in>set holders. realization_units
      (run_realization certificates (realization_plan_from roots holders values target) m) root h=target root h)"
  using financial credited keys initial masses
proof (induction roots arbitrary:m)
  case Nil
  then show ?case by (simp add: realization_plan_from_def)
next
  case (Cons root roots)
  let ?row = "realization_row root holders (values root) (target root)"
  let ?next = "run_realization certificates ?row m"
  let ?rest = "realization_plan_from roots holders values target"
  have root_credit: "root\<in>set (credit_history (received_messages (machine_state m)))"
    using Cons.prems(2) by simp
  have root_initial: "\<forall>h\<in>set holders. realization_units m root h=values root h"
    using Cons.prems(4) by simp
  have root_mass: "sum_list (map (target root) holders)=sum_list (map (values root) holders)"
    using Cons.prems(5) by simp
  have first: "realization_succeeds certificates ?row m \<and>
    (\<forall>h\<in>set holders. realization_units ?next root h=target root h)"
    by (rule realization_row_is_constructive[OF Cons.prems(1) root_credit holders root_initial root_mass])
  have next_financial: "financial_history_agreement balances ?next"
    by (rule run_realization_financial[OF Cons.prems(1)]) (use first in blast)
  have next_credits: "\<forall>r\<in>set roots. r\<in>set (credit_history (received_messages (machine_state ?next)))"
    using Cons.prems(2) by simp
  have next_keys: "distinct (map binding_key roots)" using Cons.prems(3) by simp
  have distinct_key: "\<And>r. r\<in>set roots \<Longrightarrow> binding_key r\<noteq>binding_key root"
  proof -
    fix r assume member: "r\<in>set roots"
    have present: "binding_key r\<in>binding_key ` set roots"
      by (rule imageI[OF member])
    have absent: "binding_key root\<notin>binding_key ` set roots"
      using Cons.prems(3) by simp
    show "binding_key r\<noteq>binding_key root"
    proof (rule notI)
      assume equal: "binding_key r=binding_key root"
      have hit: "binding_key root\<in>binding_key ` set roots"
        using present by (simp only: equal)
      show False by (rule notE[OF absent hit])
    qed
  qed
  have next_initial: "\<forall>r\<in>set roots. \<forall>h\<in>set holders. realization_units ?next r h=values r h"
  proof (intro ballI)
    fix r h assume r: "r\<in>set roots" and h: "h\<in>set holders"
    have frame: "realization_units ?next r h=realization_units m r h"
      unfolding realization_units_def
    proof (rule run_realization_funding_frame)
      show "\<forall>e\<in>set ?row. binding_key r\<noteq>binding_key (lineage_root e) \<or>
        (holder_account r h\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
          holder_account r h\<noteq>holder_account (lineage_root e) (lineage_to e))"
        using distinct_key[OF r] realization_row_support by blast
    qed
    show "realization_units ?next r h=values r h" using frame Cons.prems(4) r h by simp
  qed
  have next_masses: "\<forall>r\<in>set roots. sum_list (map (target r) holders)=sum_list (map (values r) holders)"
    using Cons.prems(5) by simp
  have tail: "realization_succeeds certificates ?rest ?next \<and>
    (\<forall>r\<in>set roots. \<forall>h\<in>set holders. realization_units
      (run_realization certificates ?rest ?next) r h=target r h)"
    by (rule Cons.IH[OF next_financial next_credits next_keys next_initial next_masses])
  have head_frame: "\<And>h. realization_units (run_realization certificates ?rest ?next) root h=
      realization_units ?next root h"
    unfolding realization_units_def
  proof (rule run_realization_funding_frame)
    fix h
    show "\<forall>e\<in>set ?rest. binding_key root\<noteq>binding_key (lineage_root e) \<or>
      (holder_account root h\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
        holder_account root h\<noteq>holder_account (lineage_root e) (lineage_to e))"
    proof (intro ballI)
      fix e assume member: "e\<in>set ?rest"
      have root_member: "lineage_root e\<in>set roots"
        by (rule conjunct1[OF realization_plan_support[OF member]])
      have key_different: "binding_key (lineage_root e)\<noteq>binding_key root"
        by (rule distinct_key[OF root_member])
      have reverse: "binding_key root\<noteq>binding_key (lineage_root e)"
        using key_different by (simp only: eq_commute HOL.simp_thms)
      show "binding_key root\<noteq>binding_key (lineage_root e) \<or>
        (holder_account root h\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
          holder_account root h\<noteq>holder_account (lineage_root e) (lineage_to e))"
        by (rule disjI1[OF reverse])
    qed
  qed
  show ?case using first tail head_frame
    by (simp add: realization_plan_from_Cons realization_succeeds_append run_realization_append)
qed

section \<open>The Actual Pooled Balance Follows the Selected Root Changes\<close>

lemma realization_result_integer_changes:
  assumes financial: "financial_history_agreement balances m"
    and success: "snd (realization_result certificates e m)=Descendant_Executed"
  defines "next \<equiv> fst (realization_result certificates e m)"
    and "effect \<equiv> realization_effect (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)"
  shows "int (destination_units (machine_state next) account) =
      int (destination_units (machine_state m) account)+descendant_delta account effect"
    and "int (funded_units (machine_state next) (key,account)) =
      int (funded_units (machine_state m) (key,account))+
        (if binding_key (lineage_root e)=key then descendant_delta account effect else 0)"
proof -
  have after_financial: "financial_history_agreement balances next"
    unfolding next_def by (rule realization_result_financial[OF financial success])
  have credits: "received_messages (machine_state next)=received_messages (machine_state m)"
    by (simp add: next_def)
  have history: "lawful_descendants (machine_state next)=lawful_descendants (machine_state m)@[effect]"
    by (simp add: next_def realization_result_commits[OF success] effect_def
        record_observation_def commit_reservation_event_def realization_effect_def Let_def)
  have before_destination: "int (destination_units (machine_state m) account) =
    destination_credits (machine_state m) account+
      sum_list (map (descendant_delta account) (lawful_descendants (machine_state m)))"
    using financial unfolding financial_history_agreement_def by blast
  have after_destination: "int (destination_units (machine_state next) account) =
    destination_credits (machine_state next) account+
      sum_list (map (descendant_delta account) (lawful_descendants (machine_state next)))"
    using after_financial unfolding financial_history_agreement_def by blast
  have destination_credit: "destination_credits (machine_state next) account=destination_credits (machine_state m) account"
    by (simp add: destination_credits_def credits)
  show "int (destination_units (machine_state next) account) =
      int (destination_units (machine_state m) account)+descendant_delta account effect"
    using before_destination after_destination
    by (simp add: history destination_credit add.assoc)
  have before_root: "int (funded_units (machine_state m) (key,account)) =
    root_credits (machine_state m) key account+
      sum_list (map (\<lambda>d. if binding_key (lineage_root d)=key then descendant_delta account d else 0)
        (lawful_descendants (machine_state m)))"
    using financial unfolding financial_history_agreement_def by blast
  have after_root: "int (funded_units (machine_state next) (key,account)) =
    root_credits (machine_state next) key account+
      sum_list (map (\<lambda>d. if binding_key (lineage_root d)=key then descendant_delta account d else 0)
        (lawful_descendants (machine_state next)))"
    using after_financial unfolding financial_history_agreement_def by blast
  have root_credit: "root_credits (machine_state next) key account=root_credits (machine_state m) key account"
    by (simp add: root_credits_def credits)
  show "int (funded_units (machine_state next) (key,account)) =
      int (funded_units (machine_state m) (key,account))+
        (if binding_key (lineage_root e)=key then descendant_delta account effect else 0)"
    using before_root after_root
    by (simp add: history root_credit effect_def realization_effect_def add.assoc)
qed

lemma realization_sum_single_change:
  fixes before after :: "'a \<Rightarrow> int"
  assumes unique: "distinct entries" and member: "entry\<in>set entries"
    and frame: "\<forall>x\<in>set entries. x\<noteq>entry \<longrightarrow> after x=before x"
  shows "sum_list (map after entries)-sum_list (map before entries)=after entry-before entry"
  using assms
proof (induction entries)
  case Nil
  then show ?case by simp
next
  case (Cons x entries)
  show ?case
  proof (cases "x=entry")
    case True
    have tail: "map after entries=map before entries"
      by (rule map_cong[OF refl]) (use Cons.prems True in auto)
    show ?thesis by (simp add: True tail)
  next
    case False
    have tail_unique: "distinct entries" using Cons.prems(1) by simp
    have tail_member: "entry\<in>set entries" using Cons.prems(2) False by simp
    have tail_frame: "\<forall>y\<in>set entries. y\<noteq>entry \<longrightarrow> after y=before y"
      using Cons.prems(3) by simp
    have tail: "sum_list (map after entries)-sum_list (map before entries)=after entry-before entry"
      by (rule Cons.IH[OF tail_unique tail_member tail_frame])
    have head: "after x=before x" using Cons.prems(3) False by simp
    show ?thesis using tail by (simp add: head)
  qed
qed

definition realization_residual :: "transfer_binding list \<Rightarrow> reservation_machine \<Rightarrow>
  destination_account \<Rightarrow> int" where
  "realization_residual roots m account = int (destination_units (machine_state m) account)-
    sum_list (map (\<lambda>root. int (funded_units (machine_state m) (binding_key root,account))) roots)"

lemma realization_result_residual:
  assumes financial: "financial_history_agreement balances m"
    and success: "snd (realization_result certificates e m)=Descendant_Executed"
    and unique: "distinct (map binding_key roots)"
    and member: "lineage_root e\<in>set roots"
  shows "realization_residual roots (fst (realization_result certificates e m)) account=
    realization_residual roots m account"
proof -
  let ?next = "fst (realization_result certificates e m)"
  let ?before = "\<lambda>root. int (funded_units (machine_state m) (binding_key root,account))"
  let ?after = "\<lambda>root. int (funded_units (machine_state ?next) (binding_key root,account))"
  let ?delta = "descendant_delta account
    (realization_effect (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e))"
  have both: "distinct roots \<and> inj_on binding_key (set roots)"
    by (rule unique[unfolded distinct_map])
  have distinct: "distinct roots" by (rule conjunct1[OF both])
  have injective: "inj_on binding_key (set roots)" by (rule conjunct2[OF both])
  have frame: "\<forall>r\<in>set roots. r\<noteq>lineage_root e \<longrightarrow> ?after r=?before r"
  proof (intro ballI impI)
    fix r assume r: "r\<in>set roots" and different: "r\<noteq>lineage_root e"
    have key_different: "binding_key (lineage_root e)\<noteq>binding_key r"
    proof (rule notI)
      assume equal: "binding_key (lineage_root e)=binding_key r"
      have same: "r=lineage_root e"
        by (rule inj_onD[OF injective equal[symmetric] r member])
      show False by (rule notE[OF different same])
    qed
    show "?after r=?before r"
      using realization_result_integer_changes(2)[OF financial success, where key="binding_key r" and account=account]
      by (simp add: key_different)
  qed
  have sum_change: "sum_list (map ?after roots)-sum_list (map ?before roots)=?after (lineage_root e)-?before (lineage_root e)"
    by (rule realization_sum_single_change[OF distinct member frame])
  have root_change: "?after (lineage_root e)=?before (lineage_root e)+?delta"
    using realization_result_integer_changes(2)[OF financial success,
      where key="binding_key (lineage_root e)" and account=account] by simp
  have pool_change: "int (destination_units (machine_state ?next) account)=
      int (destination_units (machine_state m) account)+?delta"
    using realization_result_integer_changes(1)[OF financial success, where account=account] by simp
  show ?thesis unfolding realization_residual_def using sum_change root_change pool_change by linarith
qed

lemma run_realization_residual:
  assumes financial: "financial_history_agreement balances m"
    and success: "realization_succeeds certificates effects m"
    and unique: "distinct (map binding_key roots)"
    and members: "\<forall>e\<in>set effects. lineage_root e\<in>set roots"
  shows "realization_residual roots (run_realization certificates effects m) account=
    realization_residual roots m account"
  using financial success members
proof (induction effects arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons e effects)
  have reply: "snd (realization_result certificates e m)=Descendant_Executed"
    using Cons.prems(2) by simp
  have member: "lineage_root e\<in>set roots" using Cons.prems(3) by simp
  have head: "realization_residual roots (fst (realization_result certificates e m)) account=
      realization_residual roots m account"
    by (rule realization_result_residual[OF Cons.prems(1) reply unique member])
  have next_financial: "financial_history_agreement balances (fst (realization_result certificates e m))"
    by (rule realization_result_financial[OF Cons.prems(1) reply])
  have tail: "realization_residual roots
      (run_realization certificates effects (fst (realization_result certificates e m))) account=
      realization_residual roots (fst (realization_result certificates e m)) account"
    by (rule Cons.IH[OF next_financial]) (use Cons.prems(2,3) in simp_all)
  show ?case using head tail by simp
qed

definition realization_cells :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow>
  (source_key \<times> destination_account) set" where
  "realization_cells roots holders =
    {(binding_key root,holder_account root h) | root h. root\<in>set roots \<and> h\<in>set holders}"

lemma realization_cell_member:
  assumes "root\<in>set roots" "h\<in>set holders"
  shows "(binding_key root,holder_account root h)\<in>realization_cells roots holders"
  unfolding realization_cells_def
  by (rule CollectI, rule exI[of _ root], rule exI[of _ h]) (use assms in simp)

lemma realization_plan_outside_frame:
  assumes outside: "(key,account)\<notin>realization_cells roots holders"
  shows "funded_units (machine_state
    (run_realization certificates (realization_plan_from roots holders values target) m)) (key,account)=
      funded_units (machine_state m) (key,account)"
proof (rule run_realization_funding_frame)
  show "\<forall>e\<in>set (realization_plan_from roots holders values target).
    key\<noteq>binding_key (lineage_root e) \<or>
    (account\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
      account\<noteq>holder_account (lineage_root e) (lineage_to e))"
  proof (intro ballI)
    fix e assume member: "e\<in>set (realization_plan_from roots holders values target)"
    have root_member: "lineage_root e\<in>set roots"
      and from_member: "lineage_from e\<in>set holders"
      and to_member: "lineage_to e\<in>set holders"
      using realization_plan_support[OF member] by blast+
    show "key\<noteq>binding_key (lineage_root e) \<or>
      (account\<noteq>holder_account (lineage_root e) (lineage_from e) \<and>
        account\<noteq>holder_account (lineage_root e) (lineage_to e))"
    proof (cases "key=binding_key (lineage_root e)")
      case False
      show ?thesis by (rule disjI1[OF False])
    next
      case True
      have from_cell: "(binding_key (lineage_root e),holder_account (lineage_root e) (lineage_from e))
          \<in>realization_cells roots holders"
        by (rule realization_cell_member[OF root_member from_member])
      have to_cell: "(binding_key (lineage_root e),holder_account (lineage_root e) (lineage_to e))
          \<in>realization_cells roots holders"
        by (rule realization_cell_member[OF root_member to_member])
      have from_separate: "account\<noteq>holder_account (lineage_root e) (lineage_from e)"
      proof (rule notI)
        assume equal: "account=holder_account (lineage_root e) (lineage_from e)"
        have hit: "(key,account)\<in>realization_cells roots holders"
          using from_cell by (simp only: True equal)
        show False by (rule notE[OF outside hit])
      qed
      have to_separate: "account\<noteq>holder_account (lineage_root e) (lineage_to e)"
      proof (rule notI)
        assume equal: "account=holder_account (lineage_root e) (lineage_to e)"
        have hit: "(key,account)\<in>realization_cells roots holders"
          using to_cell by (simp only: True equal)
        show False by (rule notE[OF outside hit])
      qed
      show ?thesis by (rule disjI2, rule conjI[OF from_separate to_separate])
    qed
  qed
qed

definition realization_account_total :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow>
  (transfer_binding \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> destination_account \<Rightarrow> int" where
  "realization_account_total roots holders values account =
    sum_list (map (\<lambda>root. sum_list (map (\<lambda>h.
      if holder_account root h=account then int (values root h) else 0) holders)) roots)"

definition realization_outside_total :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow>
  reservation_machine \<Rightarrow> destination_account \<Rightarrow> int" where
  "realization_outside_total roots holders m account =
    sum_list (map (\<lambda>root. if account\<in>holder_account root ` set holders then 0
      else int (funded_units (machine_state m) (binding_key root,account))) roots)"

lemma realization_holder_single_sum:
  fixes weight :: int
  assumes "distinct holders"
  shows "sum_list (map (\<lambda>h. if holder_account root h=account then weight else 0) holders)=
    (if account\<in>holder_account root ` set holders then weight else 0)"
  using assms
proof (induction holders)
  case Nil
  then show ?case by simp
next
  case (Cons h holders)
  have tail: "sum_list (map (\<lambda>x. if holder_account root x=account then weight else 0) holders)=
    (if account\<in>holder_account root ` set holders then weight else 0)"
    by (rule Cons.IH) (use Cons.prems in simp)
  show ?case
  proof (cases "holder_account root h=account")
    case True
    have absent: "account\<notin>holder_account root ` set holders"
      using Cons.prems True by (auto simp: holder_account_def)
    show ?thesis by (simp add: True absent tail)
  next
    case False
    have reverse: "account\<noteq>holder_account root h"
    proof (rule notI)
      assume equal: "account=holder_account root h"
      have same: "holder_account root h=account" by (rule sym[OF equal])
      show False by (rule notE[OF False same])
    qed
    show ?thesis by (simp add: False reverse tail)
  qed
qed

lemma realization_actual_row_sum:
  assumes "distinct holders"
  shows "sum_list (map (\<lambda>h. if holder_account root h=account
      then int (realization_units m root h) else 0) holders)=
    (if account\<in>holder_account root ` set holders
      then int (funded_units (machine_state m) (binding_key root,account)) else 0)"
proof -
  have entries: "map (\<lambda>h. if holder_account root h=account then int (realization_units m root h) else 0) holders =
    map (\<lambda>h. if holder_account root h=account
      then int (funded_units (machine_state m) (binding_key root,account)) else 0) holders"
  proof (rule map_cong[OF refl])
    fix h assume "h\<in>set holders"
    show "(if holder_account root h=account then int (realization_units m root h) else 0)=
      (if holder_account root h=account
        then int (funded_units (machine_state m) (binding_key root,account)) else 0)"
    proof (cases "holder_account root h=account")
      case True
      show ?thesis by (simp only: True if_True realization_units_def)
    next
      case False
      show ?thesis by (simp only: False if_False)
    qed
  qed
  show ?thesis by (simp only: entries realization_holder_single_sum[OF assms])
qed

lemma realization_total_decomposition:
  assumes "distinct holders"
  shows "sum_list (map (\<lambda>root. int (funded_units (machine_state m) (binding_key root,account))) roots)=
    realization_account_total roots holders (realization_units m) account+
      realization_outside_total roots holders m account"
proof (induction roots)
  case Nil
  show ?case by (simp add: realization_account_total_def realization_outside_total_def)
next
  case (Cons root roots)
  show ?case
    using Cons.IH
    by (cases "account\<in>holder_account root ` set holders")
      (simp_all add: realization_account_total_def realization_outside_total_def
        realization_actual_row_sum[OF assms] algebra_simps)
qed

lemma realization_selected_row:
  assumes unique: "distinct (map binding_key roots)" and member: "root\<in>set roots"
  shows "(binding_key root,account)\<in>realization_cells roots holders \<longleftrightarrow>
    account\<in>holder_account root ` set holders"
proof -
  have injective: "inj_on binding_key (set roots)"
    using unique by (simp only: distinct_map; blast)
  show ?thesis
  proof
    assume selected: "(binding_key root,account)\<in>realization_cells roots holders"
    obtain other h where other: "other\<in>set roots" and h: "h\<in>set holders"
      and pair: "(binding_key root,account)=(binding_key other,holder_account other h)"
      using selected unfolding realization_cells_def by blast
    have key_equal: "binding_key root=binding_key other"
      using arg_cong[OF pair, where f=fst] by simp
    have same: "root=other" by (rule inj_onD[OF injective key_equal member other])
    have account_equal: "account=holder_account root h"
      using arg_cong[OF pair, where f=snd] by (simp only: snd_conv same)
    have present: "holder_account root h\<in>holder_account root ` set holders"
      by (rule imageI[OF h])
    show "account\<in>holder_account root ` set holders"
      using present by (simp only: account_equal)
  next
    assume selected: "account\<in>holder_account root ` set holders"
    obtain h where h: "h\<in>set holders" and account_equal: "account=holder_account root h"
      using selected by blast
    have present: "(binding_key root,holder_account root h)\<in>realization_cells roots holders"
      by (rule realization_cell_member[OF member h])
    show "(binding_key root,account)\<in>realization_cells roots holders"
      using present by (simp only: account_equal)
  qed
qed

lemma realization_account_totals_restore_pooled:
  assumes keys: "distinct (map binding_key roots)" and unique: "distinct holders"
    and realized: "\<forall>root\<in>set roots. \<forall>h\<in>set holders. realization_units after root h=target root h"
    and outside: "\<forall>key account. (key,account)\<notin>realization_cells roots holders \<longrightarrow>
      funded_units (machine_state after) (key,account)=funded_units (machine_state before) (key,account)"
    and columns: "\<forall>account. realization_account_total roots holders target account=
      realization_account_total roots holders (realization_units before) account"
    and residual: "\<forall>account. realization_residual roots after account=realization_residual roots before account"
  shows "destination_units (machine_state after)=destination_units (machine_state before)"
proof (rule ext)
  fix account
  have target_total: "realization_account_total roots holders (realization_units after) account=
      realization_account_total roots holders target account"
    unfolding realization_account_total_def
  proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
    fix root assume r: "root\<in>set roots"
    show "sum_list (map (\<lambda>h. if holder_account root h=account
      then int (realization_units after root h) else 0) holders)=
      sum_list (map (\<lambda>h. if holder_account root h=account then int (target root h) else 0) holders)"
    proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
      fix h assume member: "h\<in>set holders"
      have row: "\<forall>h\<in>set holders. realization_units after root h=target root h"
        by (rule bspec[OF realized r])
      have target_at: "realization_units after root h=target root h"
        by (rule bspec[OF row member])
      show "(if holder_account root h=account then int (realization_units after root h) else 0)=
        (if holder_account root h=account then int (target root h) else 0)"
        by (simp only: target_at)
    qed
  qed
  have outside_total: "realization_outside_total roots holders after account=
      realization_outside_total roots holders before account"
    unfolding realization_outside_total_def
  proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
    fix root assume r: "root\<in>set roots"
    show "(if account\<in>holder_account root ` set holders then 0
      else int (funded_units (machine_state after) (binding_key root,account)))=
      (if account\<in>holder_account root ` set holders then 0
      else int (funded_units (machine_state before) (binding_key root,account)))"
    proof (cases "account\<in>holder_account root ` set holders")
      case True
      show ?thesis by (simp only: True if_True)
    next
      case False
      have selected_iff: "(binding_key root,account)\<in>realization_cells roots holders \<longleftrightarrow>
          account\<in>holder_account root ` set holders"
        by (rule realization_selected_row[OF keys r])
      have absent: "(binding_key root,account)\<notin>realization_cells roots holders"
      proof (rule notI)
        assume member: "(binding_key root,account)\<in>realization_cells roots holders"
        have hit: "account\<in>holder_account root ` set holders"
          by (rule iffD1[OF selected_iff member])
        show False by (rule notE[OF False hit])
      qed
      have at_key: "\<forall>account. (binding_key root,account)\<notin>realization_cells roots holders \<longrightarrow>
        funded_units (machine_state after) (binding_key root,account)=
          funded_units (machine_state before) (binding_key root,account)"
        by (rule spec[OF outside])
      have conditional: "(binding_key root,account)\<notin>realization_cells roots holders \<longrightarrow>
        funded_units (machine_state after) (binding_key root,account)=
          funded_units (machine_state before) (binding_key root,account)"
        by (rule spec[OF at_key])
      have frame: "funded_units (machine_state after) (binding_key root,account)=
          funded_units (machine_state before) (binding_key root,account)"
        by (rule mp[OF conditional absent])
      show ?thesis by (simp only: False if_False frame)
    qed
  qed
  have columns_at: "realization_account_total roots holders target account=
      realization_account_total roots holders (realization_units before) account"
    using columns by blast
  have funding_totals: "sum_list (map (\<lambda>root. int (funded_units (machine_state after) (binding_key root,account))) roots)=
      sum_list (map (\<lambda>root. int (funded_units (machine_state before) (binding_key root,account))) roots)"
    by (simp only: realization_total_decomposition[OF unique] target_total outside_total columns_at)
  have residual_at: "realization_residual roots after account=realization_residual roots before account"
    using residual by blast
  have "int (destination_units (machine_state after) account)=int (destination_units (machine_state before) account)"
    using residual_at funding_totals unfolding realization_residual_def by linarith
  then show "destination_units (machine_state after) account=destination_units (machine_state before) account"
    by simp
qed

section \<open>Source Frames and the Exact Added Journal\<close>

definition realization_static_state :: "reservation_machine \<Rightarrow> reservation_state" where
  "realization_static_state m = (machine_state m)
    \<lparr>destination_units:=(\<lambda>_.0),funded_units:=(\<lambda>_.0),lawful_descendants:=[]\<rparr>"

lemma realization_result_static:
  "realization_static_state (fst (realization_result certificates e m))=realization_static_state m"
  by (rule reservation_state.equality)
    (simp_all add: realization_static_state_def realization_result_def execute_descendant_def
      record_observation_def commit_reservation_event_def Let_def split: if_splits)

lemma run_realization_static:
  "realization_static_state (run_realization certificates effects m)=realization_static_state m"
  by (induction effects arbitrary:m) (simp_all add: realization_result_static)

lemma realization_static_supplies_source_frame:
  assumes "realization_static_state after=realization_static_state before"
  shows "source_units (machine_state after)=source_units (machine_state before) \<and>
    source_effects (machine_state after)=source_effects (machine_state before) \<and>
    issued_certificates (machine_state after)=issued_certificates (machine_state before) \<and>
    received_messages (machine_state after)=received_messages (machine_state before) \<and>
    reservation_at (machine_state after)=reservation_at (machine_state before)"
  using arg_cong[OF assms, where f=source_units] arg_cong[OF assms, where f=source_effects]
    arg_cong[OF assms, where f=issued_certificates] arg_cong[OF assms, where f=received_messages]
    arg_cong[OF assms, where f=reservation_at]
  by (simp add: realization_static_state_def)

lemma erase_lineage_as_static:
  "erase_lineage_state m = (realization_static_state m)
    \<lparr>destination_units:=destination_units (machine_state m)\<rparr>"
  by (rule reservation_state.equality)
    (simp_all add: erase_lineage_state_def realization_static_state_def)

lemma run_realization_exact_history:
  assumes success: "realization_succeeds certificates effects m"
    and canonical: "\<forall>e\<in>set effects. canonical_realization_effect e"
  shows "machine_journal (run_realization certificates effects m)=machine_journal m@map Descendant_Event effects \<and>
    lawful_descendants (machine_state (run_realization certificates effects m))=
      lawful_descendants (machine_state m)@effects"
  using assms
proof (induction effects arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons e effects)
  have success: "snd (realization_result certificates e m)=Descendant_Executed"
    using Cons.prems(1) by simp
  have exact: "realization_effect (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)=e"
    using Cons.prems(2) unfolding canonical_realization_effect_def by simp
  have head_journal: "machine_journal (fst (realization_result certificates e m))=machine_journal m@[Descendant_Event e]"
    by (simp add: realization_result_commits[OF success] exact record_observation_def commit_reservation_event_def)
  have head_descendants: "lawful_descendants (machine_state (fst (realization_result certificates e m)))=
      lawful_descendants (machine_state m)@[e]"
    by (simp add: realization_result_commits[OF success] exact record_observation_def commit_reservation_event_def Let_def)
  have tail: "machine_journal (run_realization certificates effects (fst (realization_result certificates e m)))=
      machine_journal (fst (realization_result certificates e m))@map Descendant_Event effects \<and>
    lawful_descendants (machine_state (run_realization certificates effects (fst (realization_result certificates e m))))=
      lawful_descendants (machine_state (fst (realization_result certificates e m)))@effects"
    by (rule Cons.IH) (use Cons.prems in simp_all)
  show ?case using tail head_journal head_descendants by simp
qed

lemma realization_factory_supplies_current_authorization:
  "current_use_allowed
    (lock_authority (funding_probe_context (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)))
    (funding_probe_request certificate (lineage_root e) (lineage_to e) (lineage_amount e))"
  "metadata_permission
    (funding_probe_context (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e))
    (funding_probe_request certificate (lineage_root e) (lineage_to e) (lineage_amount e))
    (binding_destination (lineage_root e))"
  "valid_state (lock_metadata
    (funding_probe_context (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)))"
  by (rule funding_probe_uses_actual_current_authorization)+

lemma realization_empty_holders [simp]:
  "realization_plan roots [] m target=[]"
  by (simp add: realization_plan_def realization_plan_from_def)

lemma realization_empty_roots [simp]:
  "realization_plan [] holders m target=[]"
  by (simp add: realization_plan_def realization_plan_from_def)

context source_attestation
begin

lemma realization_run_is_parent_execution:
  "run_realization certificates effects m =
    run_reservations balances (realization_actions certificates effects) m"
  by (induction effects arbitrary:m)
    (simp_all add: realization_actions_def realization_action_def realization_result_def)

theorem finite_funding_realization:
  fixes certificates :: "transfer_binding \<Rightarrow> source_certificate"
    and effects :: "descendant_effect list"
  assumes contract: "reservation_contract balances m"
    and credited: "\<forall>root\<in>set roots. root\<in>set (credit_history (received_messages (machine_state m)))"
    and keys: "distinct (map binding_key roots)"
    and holders: "distinct holders"
    and rows: "\<forall>root\<in>set roots. sum_list (map (target root) holders)=
      sum_list (map (realization_units m root) holders)"
    and columns: "\<forall>account. realization_account_total roots holders target account=
      realization_account_total roots holders (realization_units m) account"
  defines "effects \<equiv> realization_plan roots holders m target"
    and "after \<equiv> run_reservations balances (realization_actions certificates effects) m"
  shows "realization_succeeds certificates effects m \<and>
    (\<forall>root\<in>set roots. \<forall>h\<in>set holders. realization_units after root h=target root h) \<and>
    (\<forall>key account. (key,account)\<notin>realization_cells roots holders \<longrightarrow>
      funded_units (machine_state after) (key,account)=funded_units (machine_state m) (key,account)) \<and>
    destination_units (machine_state after)=destination_units (machine_state m) \<and>
    erase_lineage_state after=erase_lineage_state m \<and>
    realization_static_state after=realization_static_state m \<and>
    machine_journal after=machine_journal m@map Descendant_Event effects \<and>
    lawful_descendants (machine_state after)=lawful_descendants (machine_state m)@effects \<and>
    (\<forall>e\<in>set effects. lineage_root e\<in>set roots \<and>
      lineage_from e\<in>set holders \<and> lineage_to e\<in>set holders \<and>
      0<lineage_amount e \<and> canonical_realization_effect e) \<and>
    reservation_contract balances after"
proof -
  have financial: "financial_history_agreement balances m"
    using contract unfolding reservation_contract_def by blast
  have run: "after=run_realization certificates effects m"
    unfolding after_def by (rule sym[OF realization_run_is_parent_execution])
  have arithmetic: "realization_succeeds certificates effects m \<and>
    (\<forall>root\<in>set roots. \<forall>h\<in>set holders. realization_units after root h=target root h)"
    unfolding run effects_def realization_plan_def
    by (rule realization_plan_from_is_constructive[OF financial credited keys holders])
      (use rows in simp_all)
  have success: "realization_succeeds certificates effects m" using arithmetic by blast
  have realized: "\<forall>root\<in>set roots. \<forall>h\<in>set holders. realization_units after root h=target root h"
    using arithmetic by blast
  have outside: "\<forall>key account. (key,account)\<notin>realization_cells roots holders \<longrightarrow>
    funded_units (machine_state after) (key,account)=funded_units (machine_state m) (key,account)"
    unfolding run effects_def realization_plan_def
  proof (intro allI impI)
    fix key account assume absent: "(key,account)\<notin>realization_cells roots holders"
    show "funded_units (machine_state (run_realization certificates
        (realization_plan_from roots holders (realization_units m) target) m)) (key,account)=
      funded_units (machine_state m) (key,account)"
      by (rule realization_plan_outside_frame[OF absent])
  qed
  have support: "\<forall>e\<in>set effects. lineage_root e\<in>set roots \<and>
    lineage_from e\<in>set holders \<and> lineage_to e\<in>set holders \<and>
    0<lineage_amount e \<and> canonical_realization_effect e"
    unfolding effects_def realization_plan_def
  proof (intro ballI)
    fix e assume member: "e\<in>set (realization_plan_from roots holders (realization_units m) target)"
    show "lineage_root e\<in>set roots \<and> lineage_from e\<in>set holders \<and>
      lineage_to e\<in>set holders \<and> 0<lineage_amount e \<and> canonical_realization_effect e"
      by (rule realization_plan_support[OF member])
  qed
  have residual: "\<forall>account. realization_residual roots after account=realization_residual roots m account"
    unfolding run
    by (intro allI, rule run_realization_residual[OF financial success keys]) (use support in blast)
  have pooled: "destination_units (machine_state after)=destination_units (machine_state m)"
    by (rule realization_account_totals_restore_pooled[OF keys holders realized outside columns residual])
  have static: "realization_static_state after=realization_static_state m"
    by (simp add: run run_realization_static)
  have erased: "erase_lineage_state after=erase_lineage_state m"
    by (simp only: erase_lineage_as_static static pooled)
  have canonical: "\<forall>e\<in>set effects. canonical_realization_effect e" using support by blast
  have history: "machine_journal after=machine_journal m@map Descendant_Event effects \<and>
    lawful_descendants (machine_state after)=lawful_descendants (machine_state m)@effects"
    unfolding run by (rule run_realization_exact_history[OF success canonical])
  have next_contract: "reservation_contract balances after"
    unfolding after_def by (rule finite_execution_preserves_reservation_contract[OF contract])
  show ?thesis using success realized outside pooled erased static history support next_contract by blast
qed

theorem finite_realization_preserves_source_allocation:
  fixes certificates :: "transfer_binding \<Rightarrow> source_certificate"
    and effects :: "descendant_effect list"
  assumes contract: "reservation_contract balances m"
  defines "after \<equiv> run_reservations balances (realization_actions certificates effects) m"
  shows "source_units (machine_state after)=source_units (machine_state m) \<and>
    source_effects (machine_state after)=source_effects (machine_state m) \<and>
    issued_certificates (machine_state after)=issued_certificates (machine_state m) \<and>
    received_messages (machine_state after)=received_messages (machine_state m) \<and>
    reservation_at (machine_state after)=reservation_at (machine_state m) \<and>
    int (source_units (machine_state after) pool)+unresolved_pool_mass (machine_state after) pool+
      destination_pool_funding (machine_state after) pool=int (balances pool)"
proof -
  have static: "realization_static_state after=realization_static_state m"
    by (simp only: after_def realization_run_is_parent_execution[symmetric] run_realization_static)
  have frame: "source_units (machine_state after)=source_units (machine_state m) \<and>
    source_effects (machine_state after)=source_effects (machine_state m) \<and>
    issued_certificates (machine_state after)=issued_certificates (machine_state m) \<and>
    received_messages (machine_state after)=received_messages (machine_state m) \<and>
    reservation_at (machine_state after)=reservation_at (machine_state m)"
    by (rule realization_static_supplies_source_frame[OF static])
  have next_contract: "reservation_contract balances after"
    unfolding after_def by (rule finite_execution_preserves_reservation_contract[OF contract])
  show ?thesis using frame provider_preserves_source_allocation[OF next_contract, of pool] by blast
qed

theorem successful_realization_has_no_new_source_credit_or_return_event:
  fixes balances :: "source_account \<Rightarrow> nat"
  assumes success: "realization_succeeds certificates effects m"
    and canonical: "\<forall>e\<in>set effects. canonical_realization_effect e"
  defines "after \<equiv> run_reservations balances (realization_actions certificates effects) m"
  shows "\<forall>b. Source_Effect_Event b\<notin>set (drop (length (machine_journal m)) (machine_journal after)) \<and>
    Credit_Event b\<notin>set (drop (length (machine_journal m)) (machine_journal after)) \<and>
    Return_Event b\<notin>set (drop (length (machine_journal m)) (machine_journal after))"
proof -
  have journal: "machine_journal after=machine_journal m@map Descendant_Event effects"
    using conjunct1[OF run_realization_exact_history[OF success canonical]]
    by (simp only: after_def realization_run_is_parent_execution[symmetric])
  show ?thesis by (auto simp: journal)
qed

end

section \<open>A Fixed Denying Policy Remains a Counterexample\<close>

theorem empty_current_spend_policy_performs_no_realization_move:
  "snd (execute_descendant (context\<lparr>lock_spend_permissions:={}\<rparr>)
    request root sender recipient amount m)=Request_Rejected \<and>
   machine_state (fst (execute_descendant (context\<lparr>lock_spend_permissions:={}\<rparr>)
    request root sender recipient amount m))=machine_state m"
  by (simp add: execute_descendant_def record_observation_def Let_def)

text \<open>The constructed word supplies the existing current singleton authority,
  exact spend permission and valid ACTIVE metadata at each positive transfer.
  Zero quantities produce no action. The certificate parameter is typed but is
  not read by the descendant consumer; no new certificate is issued or authenticated.
  Distinct immutable root keys allow the rows to share actual destination accounts.
  Column totals compare those complete accounts, including destination and asset.

  The final erased reservation state is restored. Intermediate pooled balances,
  the added descendant history and the exact journal remain observable. A fixed
  denying policy blocks the construction. This theorem uses the actual parent
  operation; the child terminal-record, publication and current-view guards need
  a separate dispatcher connection. No physical adapter or compiled API follows
  from the parent allocation equation alone.\<close>

end
