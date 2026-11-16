theory EAB_Primary_Repair
  imports DOSP_Recovery.Domain_Recovery Evidence_Atomic_Binding.Finality_Records
    "HOL-Library.Nat_Bijection"
begin

record eab_primary_receipt =
  published_key :: source_key
  published_sequence :: nat
  published_binding :: transfer_binding
  published_kind :: terminal_kind

record eab_primary_authority =
  terminal_authority :: finality_core
  publication_slots :: "nat \<Rightarrow> source_key option"

definition published_transfer_receipt ::
  "source_key \<Rightarrow> nat \<Rightarrow> finality_core \<Rightarrow> eab_primary_receipt option"
where
  "published_transfer_receipt key sequence core =
    (case core_records core key of
      None \<Rightarrow> None
    | Some terminal \<Rightarrow>
      if key \<in> core_published core \<and> binding_key (terminal_binding terminal) = key \<and>
        binding_operation (terminal_binding terminal) = Destination_Credit
      then Some \<lparr>published_key = key, published_sequence = sequence,
        published_binding = terminal_binding terminal, published_kind = terminal_kind terminal\<rparr>
      else None)"

lemma publication_receipt_ignores_protocol_epoch:
  "published_transfer_receipt key sequence (core\<lparr>core_epoch := epoch\<rparr>) =
    published_transfer_receipt key sequence core"
  by (cases "core_records core key") (simp_all add: published_transfer_receipt_def)

fun decision_tag :: "terminal_kind \<Rightarrow> nat" where
  "decision_tag Confirmed_Decision = 0"
| "decision_tag Reversed_Decision = 1"

definition primary_transfer_value :: "eab_primary_receipt \<Rightarrow> nat" where
  "primary_transfer_value receipt =
    prod_encode (decision_tag (published_kind receipt), binding_amount (published_binding receipt))"

definition primary_receipt_matches ::
  "eab_primary_authority \<Rightarrow> eab_primary_receipt \<Rightarrow> 'd recovery_state \<Rightarrow> bool"
where
  "primary_receipt_matches authority receipt s \<longleftrightarrow>
    publication_slots authority (published_sequence receipt) = Some (published_key receipt) \<and>
    published_transfer_receipt (published_key receipt) (published_sequence receipt)
      (terminal_authority authority) = Some receipt \<and>
    primary_sequence s = published_sequence receipt \<and>
    primary_record s = primary_transfer_value receipt \<and>
    irreversible_facts s = image prod_encode (core_published (terminal_authority authority))"

fun replica_repair :: "'d repair_action \<Rightarrow> bool" where
  "replica_repair (Apply_Repair _ _) = True"
| "replica_repair (Governance_Resync _ _ _) = True"
| "replica_repair _ = False"

definition receipt_repair_step ::
  "'d routing_grants \<Rightarrow> nat set \<Rightarrow> eab_primary_authority \<Rightarrow> eab_primary_receipt \<Rightarrow>
    ('d recovery_state, 'd repair_action, 'd repair_result) step_rel"
where
  "receipt_repair_step grants governance core receipt s action result t \<longleftrightarrow>
    replica_repair action \<and>
    (if primary_receipt_matches core receipt s then recovery_step grants governance s action result t
     else result = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s)"

lemma receipt_mismatch_blocks_replica_repair:
  assumes "replica_repair action" "\<not> primary_receipt_matches core receipt s"
  shows "receipt_repair_step grants governance core receipt s action result t \<longleftrightarrow>
     result = transition_result.Operational_Failure Evidence_Unavailable \<and> t = s"
  using assms by (simp add: receipt_repair_step_def)

lemma recovery_keeps_the_primary_receipt:
  assumes "recovery_step grants governance s action result t"
  shows "primary_receipt_matches authority receipt t = primary_receipt_matches authority receipt s"
  using assms by (cases rule: recovery_step.cases) (simp_all add: primary_receipt_matches_def install_replica_def)

definition fixed_primary_step ::
  "'d routing_grants \<Rightarrow> nat set \<Rightarrow> eab_primary_authority \<Rightarrow> eab_primary_receipt \<Rightarrow>
    ('d recovery_state, 'd repair_action, 'd repair_result) step_rel"
where
  "fixed_primary_step grants governance authority receipt s action result t \<longleftrightarrow>
    (if replica_repair action then receipt_repair_step grants governance authority receipt s action result t
     else recovery_step grants governance s action result t)"

lemma bound_primary_step_projects_to_recovery:
  assumes "primary_receipt_matches authority receipt s"
  shows "fixed_primary_step grants governance authority receipt s action result t =
    recovery_step grants governance s action result t"
  using assms by (simp add: fixed_primary_step_def receipt_repair_step_def)

theorem fixed_primary_repair_finishes_under_finite_interference:
  fixes events :: "nat \<Rightarrow> 'd repair_event"
  assumes run: "infinite_run (fixed_primary_step grants governance authority receipt) initial
      {s \<in> recovery_carrier. primary_receipt_matches authority receipt s} events"
    and finite: "finite {i. affects_recovery (events i)}"
    and selected: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> \<not> affects_recovery (events j)) \<Longrightarrow>
       pending_ids (source_state (events i)) \<noteq> {} \<Longrightarrow>
       \<exists>j\<ge>i. \<exists>w d seq. step_outcome (events j) = transition_result.Accepted (Installed w d seq)"
  shows "\<exists>n. \<forall>i\<ge>n.
    pending_ids (source_state (events i)) = {} \<and>
    (\<forall>d\<in>active_domains (source_state (events i)).
      replica (source_state (events i)) d = primary_transfer_value receipt) \<and>
    (\<forall>j\<le>i. pending_ids (source_state (events j)) \<union> completion_log (source_state (events j))
      \<subseteq> completion_log (source_state (events i)))"
proof -
  have states: "\<And>i. source_state (events i) \<in> recovery_carrier"
    and matched: "\<And>i. primary_receipt_matches authority receipt (source_state (events i))"
    and steps: "\<And>i. step_occurs (fixed_primary_step grants governance authority receipt) (events i)"
    using run unfolding infinite_run_def by blast+
  have projected: "\<And>i. step_occurs (recovery_step grants governance) (events i)"
  proof -
    fix i
    from steps[of i] show "step_occurs (recovery_step grants governance) (events i)"
      by (simp only: step_occurs_def bound_primary_step_projects_to_recovery[OF matched[of i]])
  qed
  have original: "infinite_run (recovery_step grants governance) initial recovery_carrier events"
    using run states projected unfolding infinite_run_def by blast
  have primary: "\<And>i. primary_record (source_state (events i)) = primary_transfer_value receipt"
    using matched by (simp add: primary_receipt_matches_def)
  show ?thesis
    using recovery_finishes_under_finite_interference[OF original finite selected] primary by simp
qed

lemma unpublished_terminal_is_not_an_installable_receipt:
  assumes "published_key receipt \<notin> core_published (terminal_authority authority)"
  shows "\<not> primary_receipt_matches authority receipt s"
  using assms by (auto simp: primary_receipt_matches_def published_transfer_receipt_def split: option.splits)

lemma a_sequence_selects_at_most_one_terminal:
  assumes "primary_receipt_matches authority first s" "primary_receipt_matches authority second s"
  shows "first = second"
proof -
  from assms have seq: "published_sequence first = published_sequence second"
    and first_slot: "publication_slots authority (published_sequence first) = Some (published_key first)"
    and second_slot: "publication_slots authority (published_sequence second) = Some (published_key second)"
    and first_receipt: "published_transfer_receipt (published_key first) (published_sequence first)
      (terminal_authority authority) = Some first"
    and second_receipt: "published_transfer_receipt (published_key second) (published_sequence second)
      (terminal_authority authority) = Some second"
    unfolding primary_receipt_matches_def by metis+
  have keys: "Some (published_key first) = Some (published_key second)"
    by (rule trans[OF sym[OF first_slot]]) (simp only: seq second_slot)
  have key: "published_key first = published_key second" using keys by (simp only: option.inject)
  have receipts: "Some first = Some second"
    by (rule trans[OF sym[OF first_receipt]]) (simp only: seq key second_receipt)
  show ?thesis using receipts by (simp only: option.inject)
qed

theorem receipt_install_consumes_the_actual_primary_and_completes_the_same_job:
  assumes installed: "receipt_repair_step grants governance core receipt s action (transition_result.Accepted (Installed job domain seq)) t"
  shows "recovery_step grants governance s action (transition_result.Accepted (Installed job domain seq)) t \<and>
    seq = published_sequence receipt \<and>
    replica t domain = primary_transfer_value receipt \<and>
    work_owner s job = Some domain \<and> work_owner t job = None \<and>
    job \<in> completion_log t \<and>
    irreversible_facts t = image prod_encode (core_published (terminal_authority core)) \<and>
    preserves_outside replica {domain} s t"
proof -
  have bound: "primary_receipt_matches core receipt s"
    and step: "recovery_step grants governance s action (transition_result.Accepted (Installed job domain seq)) t"
    using installed by (auto simp: receipt_repair_step_def split: if_splits)
  have released: "work_owner t job = None"
    using step by (cases rule: recovery_step.cases) (simp_all add: install_replica_def)
  show ?thesis
    using step bound released actual_install_uses_primary_record[OF step]
      recovery_never_changes_irreversible_facts[OF step]
    by (simp add: primary_receipt_matches_def)
qed

context source_attestation
begin

definition publish_at_sequence ::
  "source_key \<Rightarrow> nat \<Rightarrow> eab_primary_authority \<Rightarrow> eab_primary_authority \<times> finality_reply"
where
  "publish_at_sequence key sequence authority =
    (if publication_slots authority sequence \<noteq> None \<or> key \<in> core_published (terminal_authority authority)
      then (authority, Finality_Rejected)
      else
        let published = publish_primary key (terminal_authority authority)
        in if snd published = Primary_Published then
            (authority\<lparr>terminal_authority := finality_step (Publish_Primary key) (terminal_authority authority),
              publication_slots := (publication_slots authority)(sequence := Some key)\<rparr>, Primary_Published)
           else (authority, snd published))"

lemma publication_at_sequence_uses_the_native_step:
  assumes "publish_at_sequence key sequence authority = (t, Primary_Published)"
  shows "terminal_authority t = finality_step (Publish_Primary key) (terminal_authority authority)"
  using assms by (auto simp: publish_at_sequence_def Let_def split: if_splits)

lemma publication_cannot_replace_an_occupied_sequence:
  assumes "publication_slots authority sequence \<noteq> None"
  shows "publish_at_sequence key sequence authority = (authority, Finality_Rejected)"
  using assms by (simp add: publish_at_sequence_def)

theorem actual_primary_publication_supplies_its_transfer_receipt:
  assumes published: "publish_primary key s = (t, Primary_Published)"
    and valid: "terminal_records_valid s"
    and transfer: "core_records s key = Some rec" "binding_operation (terminal_binding rec) = Destination_Credit"
  shows "published_transfer_receipt key sequence t =
      Some \<lparr>published_key = key, published_sequence = sequence,
        published_binding = terminal_binding rec, published_kind = terminal_kind rec\<rparr> \<and>
    stable_source key = Some (terminal_statement rec)"
proof -
  have key: "binding_key (terminal_binding rec) = key" and trusted: "valid_terminal_record rec"
    using terminal_records_lookup_valid[OF valid transfer(1)] by blast+
  have post: "core_records t = core_records s" "key \<in> core_published t"
    using published transfer(1) by (auto simp: publish_primary_def split: if_splits)
  have source: "stable_source key = Some (terminal_statement rec)"
    using valid_record_has_stable_source_statement[OF trusted] key by simp
  show ?thesis
    using transfer key post source by (simp add: published_transfer_receipt_def)
qed

theorem publication_at_sequence_resolves_its_exact_terminal:
  assumes actual: "publish_at_sequence key sequence authority = (next, Primary_Published)"
    and valid: "terminal_records_valid (terminal_authority authority)"
    and at: "core_records (terminal_authority authority) key = Some rec"
    and transfer: "binding_operation (terminal_binding rec) = Destination_Credit"
  shows "publication_slots next sequence = Some key \<and>
    published_transfer_receipt key sequence (terminal_authority next) =
      Some \<lparr>published_key = key, published_sequence = sequence,
        published_binding = terminal_binding rec, published_kind = terminal_kind rec\<rparr>"
proof -
  let ?call = "publish_primary key (terminal_authority authority)"
  have raw: "snd ?call = Primary_Published"
    and slot: "publication_slots next sequence = Some key"
    using actual by (auto simp: publish_at_sequence_def Let_def split: if_splits)
  have call: "?call = (fst ?call, Primary_Published)" using raw
    by (cases ?call) simp
  have stepped: "terminal_authority next =
    (fst ?call)\<lparr>core_epoch := Suc (core_epoch (terminal_authority authority))\<rparr>"
    using publication_at_sequence_uses_the_native_step[OF actual] by (simp add: finality_step_def)
  show ?thesis
    using actual_primary_publication_supplies_its_transfer_receipt[OF call valid at transfer, of sequence] slot
    by (simp add: stepped publication_receipt_ignores_protocol_epoch)
qed

lemma source_publication_is_persistent:
  assumes "key \<in> core_published s"
  shows "key \<in> core_published (run_finality actions s)"
  using assms
proof (induction actions arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons action rest)
  have "key \<in> core_published (finality_step action s)"
    using Cons.prems by (cases action)
      (auto simp: finality_step_def record_terminal_def invoke_protocol_def reject_protocol_intent_def
        invoke_regulatory_def publish_primary_def Let_def split: option.splits if_splits)
  with Cons.IH show ?case by simp
qed

theorem continued_authority_cannot_change_a_receipt_payload:
  assumes receipt: "published_transfer_receipt key sequence s = Some receipt"
  shows "published_transfer_receipt key sequence (run_finality actions s) = Some receipt"
proof -
  obtain old where at: "core_records s key = Some old"
    and matching_key: "binding_key (terminal_binding old) = key"
    and transfer: "binding_operation (terminal_binding old) = Destination_Credit"
    and published: "key \<in> core_published s"
    and fields: "receipt = \<lparr>published_key = key, published_sequence = sequence,
      published_binding = terminal_binding old, published_kind = terminal_kind old\<rparr>"
    using receipt by (auto simp: published_transfer_receipt_def split: option.splits if_splits)
  obtain later where lookup: "core_records (run_finality actions s) key = Some later"
    and core: "terminal_core later = terminal_core old"
    using all_future_operations_keep_the_terminal_core[OF at] by blast
  have binding: "terminal_binding later = terminal_binding old" and kind: "terminal_kind later = terminal_kind old"
    using core by (simp_all add: terminal_core_def)
  show ?thesis using lookup matching_key transfer fields binding kind source_publication_is_persistent[OF published, of actions]
    by (simp add: published_transfer_receipt_def)
qed

end

end
