theory Catalog_Recovery
  imports DOSP_Progress.Recovery_Progress
begin

type_synonym release_key = "nat \<times> nat"
type_synonym copy_key = "nat \<times> release_key"

record catalog =
  mirrors :: "nat set"
  releases :: "release_key set"
  tombstones :: "release_key set"
  raw_contents :: "nat \<Rightarrow> release_key set"
  catalogue_pending :: "copy_key set"
  catalogue_done :: "copy_key set"
  host :: "nat \<Rightarrow> nat"

datatype catalogue_action =
    Publish release_key | Withdraw release_key | Connect nat | Disconnect nat nat
  | Copy copy_key | Read_Package nat release_key | No_Catalogue_Work

datatype catalogue_success =
    Published "copy_key set" | Withdrawn release_key | Connected "copy_key set"
  | Disconnected nat | Copied copy_key | Withdrew_From_Mirror copy_key | Served release_key

type_synonym catalogue_result = "(catalogue_success, unit, unit, unit) transition_result"
type_synonym catalogue_event = "(catalog, catalogue_action, catalogue_result) transition"

definition fresh_copies :: "catalog \<Rightarrow> copy_key set \<Rightarrow> bool" where
  "fresh_copies c ids \<longleftrightarrow> ids \<inter> (catalogue_pending c \<union> catalogue_done c) = {}"

definition record_copy :: "catalog \<Rightarrow> copy_key \<Rightarrow> catalog" where
  "record_copy c job =
    c\<lparr>catalogue_pending := catalogue_pending c - {job}, catalogue_done := insert job (catalogue_done c)\<rparr>"

definition visible_catalogue :: "catalog \<Rightarrow> nat \<Rightarrow> release_key set" where
  "visible_catalogue c d = raw_contents c d - tombstones c"

inductive catalogue_step :: "(catalog, catalogue_action, catalogue_result) step_rel"
where
  Publish_To_Mirrors:
    "\<lbrakk>r \<notin> releases c; ids = mirrors c \<times> {r}; fresh_copies c ids\<rbrakk> \<Longrightarrow>
     catalogue_step c (Publish r) (Accepted (Published ids))
       (c\<lparr>releases := insert r (releases c), catalogue_pending := catalogue_pending c \<union> ids\<rparr>)"
| Withdraw_Release:
    "r \<in> releases c \<Longrightarrow> catalogue_step c (Withdraw r) (Accepted (Withdrawn r))
       (c\<lparr>tombstones := insert r (tombstones c)\<rparr>)"
| Connect_Mirror:
    "\<lbrakk>d \<notin> mirrors c; ids = {d} \<times> releases c; fresh_copies c ids\<rbrakk> \<Longrightarrow>
     catalogue_step c (Connect d) (Accepted (Connected ids))
       (c\<lparr>mirrors := insert d (mirrors c), host := (host c)(d := d),
           catalogue_pending := catalogue_pending c \<union> ids\<rparr>)"
| Disconnect_Mirror:
    "\<lbrakk>d \<in> mirrors c; successor \<in> mirrors c; d \<noteq> successor\<rbrakk> \<Longrightarrow>
     catalogue_step c (Disconnect d successor) (Accepted (Disconnected d))
       (c\<lparr>mirrors := mirrors c - {d},
           host := (\<lambda>key. if host c key = d then successor else host c key)\<rparr>)"
| Reproduce_Release:
    "\<lbrakk>job \<in> catalogue_pending c; d = host c (fst job); d \<in> mirrors c;
      r = snd job; r \<in> releases c; r \<notin> tombstones c\<rbrakk> \<Longrightarrow>
     catalogue_step c (Copy job) (Accepted (Copied job))
       ((record_copy c job)\<lparr>raw_contents := (raw_contents c)(d := insert r (raw_contents c d))\<rparr>)"
| Propagate_Withdrawal:
    "\<lbrakk>job \<in> catalogue_pending c; d = host c (fst job); d \<in> mirrors c;
      r = snd job; r \<in> tombstones c\<rbrakk> \<Longrightarrow>
     catalogue_step c (Copy job) (Accepted (Withdrew_From_Mirror job))
       ((record_copy c job)\<lparr>raw_contents := (raw_contents c)(d := raw_contents c d - {r})\<rparr>)"
| Serve:
    "\<lbrakk>d \<in> mirrors c; r \<in> visible_catalogue c d\<rbrakk> \<Longrightarrow>
      catalogue_step c (Read_Package d r) (Accepted (Served r)) c"
| Reject:
    "d \<notin> mirrors c \<or> r \<notin> visible_catalogue c d \<Longrightarrow>
      catalogue_step c (Read_Package d r) (Rejected ()) c"
| Idle:
    "catalogue_step c No_Catalogue_Work (Internal ()) c"

fun copies_admitted :: "catalogue_result \<Rightarrow> copy_key set" where
  "copies_admitted (Accepted (Published ids)) = ids"
| "copies_admitted (Accepted (Connected ids)) = ids"
| "copies_admitted _ = {}"

fun copies_finished :: "catalogue_result \<Rightarrow> copy_key set" where
  "copies_finished (Accepted (Copied job)) = {job}"
| "copies_finished (Accepted (Withdrew_From_Mirror job)) = {job}"
| "copies_finished _ = {}"

definition catalogue_interrupts :: "catalogue_result \<Rightarrow> bool" where
  "catalogue_interrupts outcome \<longleftrightarrow>
     copies_admitted outcome \<noteq> {} \<or>
     (\<exists>r. outcome = Accepted (Withdrawn r)) \<or> (\<exists>d. outcome = Accepted (Disconnected d))"

definition catalogue_carrier :: "catalog set" where
  "catalogue_carrier = {c. finite (catalogue_pending c) \<and> finite (mirrors c) \<and> finite (releases c) \<and>
    catalogue_pending c \<inter> catalogue_done c = {}}"

lemma catalogue_preserves_accounting:
  assumes "step_occurs catalogue_step e" "source_state e \<in> catalogue_carrier"
  shows "accounts_for catalogue_pending catalogue_done
    (\<lambda>x. copies_admitted (step_outcome x)) (\<lambda>x. copies_finished (step_outcome x)) e"
  using assms unfolding step_occurs_def
  by (cases rule: catalogue_step.cases)
     (auto simp: accounts_for_def catalogue_carrier_def fresh_copies_def record_copy_def)

lemma catalogue_closure:
  assumes "catalogue_step c a r t" "c \<in> catalogue_carrier"
  shows "t \<in> catalogue_carrier"
  using assms by (cases rule: catalogue_step.cases)
    (auto simp: catalogue_carrier_def fresh_copies_def record_copy_def)

lemma tombstones_are_monotone:
  "catalogue_step c a r t \<Longrightarrow> tombstones c \<subseteq> tombstones t"
  by (erule catalogue_step.cases) (auto simp: record_copy_def)

lemma a_withdrawn_release_cannot_be_served:
  "\<lbrakk>catalogue_step c (Read_Package d r) result t; r \<in> tombstones c\<rbrakk>
    \<Longrightarrow> result = Rejected ()"
  by (erule catalogue_step.cases) (auto simp: visible_catalogue_def)

lemma actual_catalogue_completion:
  assumes "catalogue_step c action result t" "job \<in> copies_finished result"
  shows "job \<in> catalogue_pending c \<and> job \<in> catalogue_done t \<and>
    (snd job \<in> raw_contents t (host c (fst job)) \<longleftrightarrow> snd job \<notin> tombstones c) \<and>
    preserves_outside raw_contents {host c (fst job)} c t"
  using assms by (cases rule: catalogue_step.cases) (auto simp: record_copy_def preserves_outside_def)

theorem catalogue_drains_under_finite_interference:
  fixes events :: "nat \<Rightarrow> catalogue_event"
  assumes run: "infinite_run catalogue_step initial catalogue_carrier events"
    and settled: "finite {i. catalogue_interrupts (step_outcome (events i))}"
    and selected:
      "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> catalogue_interrupts (step_outcome (events j))) \<Longrightarrow>
       catalogue_pending (source_state (events i)) \<noteq> {} \<Longrightarrow>
       \<exists>j\<ge>i. \<exists>job. step_outcome (events j) = Accepted (Copied job) \<or>
                               step_outcome (events j) = Accepted (Withdrew_From_Mirror job)"
  shows "\<exists>n. \<forall>i\<ge>n. catalogue_pending (source_state (events i)) = {} \<and>
    (\<forall>j\<le>i. catalogue_pending (source_state (events j)) \<union> catalogue_done (source_state (events j))
      \<subseteq> catalogue_done (source_state (events i)))"
proof -
  have balance: "\<And>i. accounts_for catalogue_pending catalogue_done
    (\<lambda>x. copies_admitted (step_outcome x)) (\<lambda>x. copies_finished (step_outcome x)) (events i)"
    using run by (auto simp: infinite_run_def intro: catalogue_preserves_accounting)
  have births: "\<And>i. copies_admitted (step_outcome (events i)) \<noteq> {} \<Longrightarrow>
    catalogue_interrupts (step_outcome (events i))"
    by (simp add: catalogue_interrupts_def)
  have work: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> catalogue_interrupts (step_outcome (events j))) \<Longrightarrow>
    catalogue_pending (source_state (events i)) \<noteq> {} \<Longrightarrow>
    \<exists>j\<ge>i. copies_finished (step_outcome (events j)) \<noteq> {}"
    using selected by (metis copies_finished.simps(1,2) insert_not_empty)
  show ?thesis
    by (rule eventual_completion_under_finite_interference[OF run balance births settled work])
qed

end
