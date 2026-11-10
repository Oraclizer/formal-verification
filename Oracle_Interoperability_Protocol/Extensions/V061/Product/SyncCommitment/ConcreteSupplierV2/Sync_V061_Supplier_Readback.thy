theory Sync_V061_Supplier_Readback
  imports "OIP_Sync_V061_Position_Provider.Sync_V061_Provider"
begin

record 'key supplier_roster =
  supplier_record_issuer :: 'key
  supplier_roster_quorum :: nat
  supplier_roster_signers :: "nat \<Rightarrow> 'key option"

type_synonym 'key supplier_registrations = "(nat \<times> nat \<times> nat) \<Rightarrow> 'key supplier_roster option"

definition supplier_rule_for where
  "supplier_rule_for rules statement =
    rules (sync_origin statement, sync_origin_epoch (sync_item statement), sync_roster statement)"

definition supplier_valid_roster where
  "supplier_valid_roster valid_key roster \<longleftrightarrow>
    (let keys = supplier_roster_signers roster in
     finite (dom keys) \<and> 0 < supplier_roster_quorum roster \<and>
     supplier_roster_quorum roster \<le> card (dom keys) \<and> inj_on keys (dom keys) \<and>
     valid_key (supplier_record_issuer roster) \<and>
     (\<forall>key. key \<in> ran keys \<longrightarrow> valid_key key \<and> key \<noteq> supplier_record_issuer roster))"

definition supplier_decode_statement where
  "supplier_decode_statement raw =
    Option.bind (sync_decode_proof (raw @ sync_word 0)) (\<lambda>(statement,votes).
      if votes = [] \<and> sync_format statement = 1 \<and> sync_claim statement = 1 \<and>
         sync_statement_bytes statement = raw then Some statement else None)"

definition supplier_record_preimage where
  "supplier_record_preimage statement =
    [111,105,112,47,115,111,117,114,99,101,45,99,111,109,109,105,116,109,101,110,116,45,114,101,99,111,114,100,47,118,49,0] @ sync_statement_bytes statement"

record supplier_signed_record =
  supplier_record_statement :: wire_bytes
  supplier_record_signature :: wire_bytes

definition supplier_authenticated_commitment ::
  "'key sync_verify \<Rightarrow> nat \<Rightarrow> 'key supplier_registrations \<Rightarrow> supplier_signed_record \<Rightarrow> sync_statement option" where
  "supplier_authenticated_commitment verify deployment rules signed =
    Option.bind (supplier_decode_statement (supplier_record_statement signed)) (\<lambda>statement.
      Option.bind (supplier_rule_for rules statement) (\<lambda>roster.
        if sync_deployment statement = deployment \<and>
           verify (supplier_record_issuer roster) (supplier_record_preimage statement) (supplier_record_signature signed)
        then Some statement else None))"

lemma supplier_authenticated_record_consumes_exact_statement_and_registered_issuer:
  assumes "supplier_authenticated_commitment verify deployment rules signed = Some statement"
  obtains roster where "supplier_rule_for rules statement = Some roster"
    "sync_deployment statement = deployment"
    "sync_statement_bytes statement = supplier_record_statement signed"
    "verify (supplier_record_issuer roster) (supplier_record_preimage statement) (supplier_record_signature signed)"
  using assms by (auto simp: supplier_authenticated_commitment_def supplier_decode_statement_def
    bind_eq_Some_conv split: prod.splits if_splits)

record supplier_journal_view =
  supplier_tips :: "sync_source_stream \<Rightarrow> sync_statement option"
  supplier_events :: "source_key set"

definition supplier_source_event where
  "supplier_source_event statement = (sync_origin statement, sync_event (sync_item statement))"

definition supplier_extend_journal where
  "supplier_extend_journal view statement =
    (if supplier_source_event statement \<in> supplier_events view then None
     else map_option (\<lambda>tips. view\<lparr>supplier_tips := tips,
              supplier_events := insert (supplier_source_event statement) (supplier_events view)\<rparr>)
       (sync_source_monotone_append (supplier_tips view) (sync_source_stream_of statement) statement))"

fun supplier_replay_commitments where
  "supplier_replay_commitments verify deployment rules [] view = Some view"
| "supplier_replay_commitments verify deployment rules (signed # rest) view =
    Option.bind (supplier_authenticated_commitment verify deployment rules signed) (\<lambda>statement.
      Option.bind (supplier_extend_journal view statement) (\<lambda>updated.
        supplier_replay_commitments verify deployment rules rest updated))"

lemma supplier_append_checks_event_and_reuses_monotone_source_append:
  assumes "supplier_extend_journal view statement = Some updated"
  shows "supplier_source_event statement \<notin> supplier_events view"
    "supplier_events updated = insert (supplier_source_event statement) (supplier_events view)"
    "sync_source_monotone_append (supplier_tips view) (sync_source_stream_of statement) statement =
      Some (supplier_tips updated)"
  using assms by (auto simp: supplier_extend_journal_def split: if_splits)

lemma supplier_replayed_event_is_refused_even_on_a_different_asset:
  assumes "supplier_extend_journal view statement = Some updated"
    "supplier_source_event replayed = supplier_source_event statement"
  shows "supplier_extend_journal updated replayed = None"
  using supplier_append_checks_event_and_reuses_monotone_source_append(2)[OF assms(1)] assms(2)
  by (simp add: supplier_extend_journal_def)

lemma supplier_reused_event_reaches_the_event_guard_when_the_other_stream_can_append:
  assumes prior: "supplier_extend_journal view statement = Some updated"
    and event: "supplier_source_event replayed = supplier_source_event statement"
    and absent: "supplier_tips updated (sync_source_stream_of replayed) = None"
    and snapshot: "sync_predecessor replayed = None"
  shows "supplier_extend_journal updated replayed = None"
    "sync_source_monotone_append (supplier_tips updated) (sync_source_stream_of replayed) replayed =
      Some ((supplier_tips updated)(sync_source_stream_of replayed := Some replayed))"
  using supplier_replayed_event_is_refused_even_on_a_different_asset[OF prior event] absent snapshot
  by (simp_all add: sync_source_monotone_append_def)

lemma supplier_replay_cannot_drop_a_seen_event:
  assumes "supplier_replay_commitments verify deployment rules records view = Some updated"
  shows "supplier_events view \<subseteq> supplier_events updated"
  using assms
proof (induction records arbitrary: view)
  case Nil
  then show ?case by simp
next
  case (Cons signed rest)
  obtain statement later where
    stepped: "supplier_extend_journal view statement = Some later"
    and tail: "supplier_replay_commitments verify deployment rules rest later = Some updated"
    using Cons.prems by (auto simp: bind_eq_Some_conv)
  have seen: "supplier_events later = insert (supplier_source_event statement) (supplier_events view)"
    by (rule supplier_append_checks_event_and_reuses_monotone_source_append(2)[OF stepped])
  have before_subset: "supplier_events view \<subseteq> supplier_events later"
    unfolding seen by (rule subsetI) simp
  have tail_subset: "supplier_events later \<subseteq> supplier_events updated"
    by (rule Cons.IH[OF tail])
  show ?case by (rule subset_trans[OF before_subset tail_subset])
qed

record 'stores supplier_stores =
  supplier_journal_store :: 'stores
  supplier_witness_store :: 'stores
  supplier_terminal_authorities :: 'stores
  supplier_commitment_authorities :: "'stores option"

record ('stores, 'digest, 'image) supplier_snapshot =
  supplier_snapshot_stores :: "'stores supplier_stores"
  supplier_snapshot_mark :: "nat \<times> 'digest"
  supplier_snapshot_image :: 'image

record ('stores, 'digest) supplier_selection =
  supplier_selection_stores :: "'stores supplier_stores"
  supplier_selection_mark :: "nat \<times> 'digest"
  supplier_selection_statement :: sync_statement
  supplier_selection_quorum :: nat

lemma supplier_token_equality_uses_all_four_components:
  fixes left right :: "('stores, 'digest) supplier_selection"
  shows "left = right \<longleftrightarrow>
    supplier_selection_stores left = supplier_selection_stores right \<and>
    supplier_selection_mark left = supplier_selection_mark right \<and>
    supplier_selection_statement left = supplier_selection_statement right \<and>
    supplier_selection_quorum left = supplier_selection_quorum right"
  by (cases left; cases right) simp

definition supplier_snapshot_cut where
  "supplier_snapshot_cut snapshot =
    \<lparr>witness_version = fst (supplier_snapshot_mark snapshot), witness_generation = 0, witness_control = snapshot\<rparr>"

definition supplier_readback where
  "supplier_readback archives journal observed =
    witnessed_current (\<lambda>archive witness. archive = witness_control witness)
      archives (supplier_snapshot_cut journal) (supplier_snapshot_cut observed)"

lemma supplier_readback_keeps_the_independent_snapshot_and_mark:
  assumes "supplier_readback archives journal observed = Some snapshot"
  shows "journal = observed" "snapshot = observed" "observed \<in> archives"
proof -
  have read: "witnessed_current (\<lambda>archive witness. archive = witness_control witness)
      archives (supplier_snapshot_cut journal) (supplier_snapshot_cut observed) = Some snapshot"
    using assms by (simp add: supplier_readback_def)
  note exact = readback_and_repair_depend_on_the_independently_selected_control[OF read]
  show "journal = observed" using exact(1) by (simp add: supplier_snapshot_cut_def)
  show "snapshot = observed" using exact(2) by (simp add: supplier_snapshot_cut_def)
  show "observed \<in> archives" using exact(3) by (auto simp: supplier_snapshot_cut_def)
qed

lemma supplier_rollback_or_unselected_archive_refuses_readback:
  assumes "journal \<noteq> observed \<or> observed \<notin> archives"
  shows "supplier_readback archives journal observed = None"
  using assms unfolding supplier_readback_def
  by (intro primary_rollback_and_missing_archive_keep_authority_unavailable)
    (auto simp: supplier_snapshot_cut_def)

definition supplier_selected_commitment where
  "supplier_selected_commitment verify deployment rules records stores archives journal observed stream =
    Option.bind (supplier_readback archives journal observed) (\<lambda>snapshot.
      if supplier_snapshot_stores snapshot \<noteq> stores \<or> fst (supplier_snapshot_mark snapshot) = 0 then None
      else Option.bind (supplier_replay_commitments verify deployment rules (records (supplier_snapshot_image snapshot))
          \<lparr>supplier_tips = (\<lambda>_. None), supplier_events = {}\<rparr>) (\<lambda>view.
        Option.bind (supplier_tips view (deployment,stream)) (\<lambda>statement.
          map_option (\<lambda>roster. \<lparr>supplier_selection_stores = stores,
            supplier_selection_mark = supplier_snapshot_mark snapshot,
            supplier_selection_statement = statement, supplier_selection_quorum = supplier_roster_quorum roster\<rparr>)
            (supplier_rule_for rules statement))))"

theorem supplier_selection_is_the_exact_store_mark_statement_and_quorum:
  assumes "supplier_selected_commitment verify deployment rules records stores archives journal observed stream = Some token"
  obtains roster where "journal = observed" "observed \<in> archives"
    "supplier_snapshot_stores observed = stores" "fst (supplier_snapshot_mark observed) > 0"
    "supplier_selection_stores token = stores"
    "supplier_selection_mark token = supplier_snapshot_mark observed"
    "supplier_rule_for rules (supplier_selection_statement token) = Some roster"
    "supplier_selection_quorum token = supplier_roster_quorum roster"
    "\<exists>view. supplier_replay_commitments verify deployment rules (records (supplier_snapshot_image observed))
       \<lparr>supplier_tips = (\<lambda>_. None), supplier_events = {}\<rparr> = Some view \<and>
       supplier_tips view (deployment,stream) = Some (supplier_selection_statement token)"
proof -
  obtain snapshot view statement roster where
    read: "supplier_readback archives journal observed = Some snapshot"
    and stores: "supplier_snapshot_stores snapshot = stores"
    and positive: "0 < fst (supplier_snapshot_mark snapshot)"
    and decoded: "supplier_replay_commitments verify deployment rules (records (supplier_snapshot_image snapshot))
      \<lparr>supplier_tips = (\<lambda>_. None), supplier_events = {}\<rparr> = Some view"
    and found: "supplier_tips view (deployment,stream) = Some statement"
    and configured: "supplier_rule_for rules statement = Some roster"
    and selected: "token = \<lparr>supplier_selection_stores = stores, supplier_selection_mark = supplier_snapshot_mark snapshot,
      supplier_selection_statement = statement, supplier_selection_quorum = supplier_roster_quorum roster\<rparr>"
    using assms by (auto simp: supplier_selected_commitment_def bind_eq_Some_conv split: if_splits)
  note independent = supplier_readback_keeps_the_independent_snapshot_and_mark[OF read]
  show thesis
    using independent stores positive decoded found configured selected by (intro that[of roster]) auto
qed

lemma supplier_selected_quorum_is_nonzero_under_the_reader_constructor_check:
  assumes chosen: "supplier_selected_commitment verify deployment rules records stores archives journal observed stream = Some token"
    and configured: "\<forall>roster \<in> ran rules. supplier_valid_roster valid_key roster"
  shows "0 < supplier_selection_quorum token"
proof -
  obtain roster where actual: "supplier_rule_for rules (supplier_selection_statement token) = Some roster"
    and size: "supplier_selection_quorum token = supplier_roster_quorum roster"
    using supplier_selection_is_the_exact_store_mark_statement_and_quorum[OF chosen] by blast
  have "roster \<in> ran rules" using actual by (auto simp: supplier_rule_for_def intro: ranI)
  then show ?thesis using configured size by (auto simp: supplier_valid_roster_def Let_def)
qed

end
