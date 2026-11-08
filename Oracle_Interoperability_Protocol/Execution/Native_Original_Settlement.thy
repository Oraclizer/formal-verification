theory Native_Original_Settlement
  imports "Native_Duplicate_Values"
begin

datatype native_applied_result = Native_No_Settlement |
  Native_Applied_Credit transfer_binding | Native_Applied_Refund transfer_binding

record native_retained_step =
  retained_step_result :: native_applied_result
  retained_step_revision_increment :: nat

fun native_settled_origin where
  "native_settled_origin Native_No_Settlement = None"
| "native_settled_origin (Native_Applied_Credit binding) = Some (binding_key binding)"
| "native_settled_origin (Native_Applied_Refund binding) = Some (binding_key binding)"

definition inserts_native_settlement where
  "inserts_native_settlement key step \<longleftrightarrow> native_settled_origin (retained_step_result step) = Some key"

text \<open>PrimarySnapshot::execute uses the pre-submit ledger cut for its
  CommitRef and uses OriginSlot.settled.get_or_insert on an accepted
  settlement. A rejected, busy, or duplicate operation does not run that
  insertion. This replay uses supplied classified rows and their revision
  increments; it is not a claim that those rows were decoded from any image.\<close>

fun native_settlement_replay where
  "native_settlement_replay key [] revision retained = (revision, retained)"
| "native_settlement_replay key (step # steps) revision retained =
    native_settlement_replay key steps (revision + retained_step_revision_increment step)
      (if inserts_native_settlement key step \<and> retained = None then Some revision else retained)"

fun applied_credit_index where
  "applied_credit_index binding index [] = None"
| "applied_credit_index binding index (entry # entries) =
    (if exact_applied_credit binding entry then Some index else applied_credit_index binding (Suc index) entries)"

lemma applied_credit_index_is_find:
  "applied_credit_index binding index log =
    map_option fst (List.find (\<lambda>(_, entry). exact_applied_credit binding entry) (enumerate index log))"
  by (induction log arbitrary: index) simp_all

lemma applied_credit_index_successor:
  "applied_credit_index binding (Suc index) log = map_option Suc (applied_credit_index binding index log)"
  by (induction log arbitrary: index) simp_all

lemma applied_credit_index_is_product_position:
  "applied_credit_index binding 0 log = original_credit_authority_position binding log"
  by (simp add: applied_credit_index_is_find original_credit_authority_position_def)

lemma replay_never_replaces_a_retained_settlement:
  "snd (native_settlement_replay key steps revision (Some original)) = Some original"
  by (induction steps arbitrary: revision) simp_all

definition native_revision_at_log_position where
  "native_revision_at_log_position revision steps index =
    revision + sum_list (map retained_step_revision_increment (take index steps))"

lemma native_revision_at_log_successor:
  "native_revision_at_log_position revision (step # steps) (Suc index) =
    native_revision_at_log_position (revision + retained_step_revision_increment step) steps index"
  by (simp add: native_revision_at_log_position_def add.assoc)

lemma matching_rows_compute_the_original_native_credit_commit:
  assumes aligned: "list_all2 (\<lambda>entry step.
      exact_applied_credit binding entry = inserts_native_settlement (binding_key binding) step) log steps"
  shows "snd (native_settlement_replay (binding_key binding) steps revision None) =
    map_option (native_revision_at_log_position revision steps) (applied_credit_index binding 0 log)"
  using aligned
proof (induction arbitrary: revision rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons entry entries step steps)
  show ?case
  proof (cases "exact_applied_credit binding entry")
    case True
    with Cons.hyps show ?thesis
      by (simp add: replay_never_replaces_a_retained_settlement native_revision_at_log_position_def)
  next
    case False
    with Cons.hyps Cons.IH show ?thesis
      by (cases "applied_credit_index binding 0 entries")
        (simp_all add: applied_credit_index_successor native_revision_at_log_successor)
  qed
qed

lemma released_reference_names_the_original_credit_log_index:
  assumes selected: "released_credit_reference permitted verified registered entry actor call_id payload origins = Some (binding, index)"
  shows "original_credit_authority_position binding
    (call_authority_log (product_calls (outcome_source (origin_outcomes origins)))) = Some index"
  using selected by (auto simp: released_credit_reference_def Let_def
    split: client_command.splits protocol_intent.splits option.splits if_splits)

definition native_slot_after_settlement_replay where
  "native_slot_after_settlement_replay binding steps revision slot =
    slot\<lparr>slot_settlement_value := snd (native_settlement_replay (binding_key binding) steps revision None)\<rparr>"

theorem native_duplicate_value_uses_the_revision_of_the_product_original_credit:
  assumes selected: "released_credit_reference permitted verified registered entry actor call_id payload origins = Some (binding, index)"
    and rows: "list_all2 (\<lambda>entry step.
      exact_applied_credit binding entry = inserts_native_settlement (binding_key binding) step)
      (call_authority_log (product_calls (outcome_source (origin_outcomes origins)))) steps"
    and binding: "duplicate_binding_value input = binding"
    and slot: "duplicate_origins_value input (binding_key binding) =
      Some (native_slot_after_settlement_replay binding steps revision prior_slot)"
    and decision: "slot_decision_value prior_slot = Some (True, decision_commit)"
    and command: "duplicate_command_value input = Native_Credit reference"
    and evidence: "duplicate_evidence_value input reference = Some (binding, True, reference)"
  shows "duplicate_return (native_duplicate_value_run input 20 duplicate_initial_registers) =
    Some (Native_Settlement True (native_revision_at_log_position revision steps index))"
proof -
  let ?slot = "native_slot_after_settlement_replay binding steps revision prior_slot"
  have first: "applied_credit_index binding 0
    (call_authority_log (product_calls (outcome_source (origin_outcomes origins)))) = Some index"
    by (simp only: applied_credit_index_is_product_position released_reference_names_the_original_credit_log_index[OF selected])
  have commit: "slot_settlement_value ?slot = Some (native_revision_at_log_position revision steps index)"
    using matching_rows_compute_the_original_native_credit_commit[OF rows, of revision] first
    by (simp add: native_slot_after_settlement_replay_def)
  have lookup: "duplicate_origins_value input (binding_key (duplicate_binding_value input)) = Some ?slot"
    using binding slot by simp
  have prior: "slot_decision_value ?slot = Some (True, decision_commit)"
    using decision by (simp add: native_slot_after_settlement_replay_def)
  have command_either: "duplicate_command_value input = Native_Credit reference \<or>
    duplicate_command_value input = Native_Refund reference" using command by simp
  have exact: "duplicate_evidence_value input reference = Some (duplicate_binding_value input, True, reference)"
    using evidence binding by simp
  show ?thesis by (rule settlement_value_uses_the_retained_commit_and_kind[OF lookup prior commit command_either exact])
qed

text \<open>The bridge derives the commit position rather than requiring a
  position equality. Alignment of native accepted rows with product entries,
  source of the revision increments, authenticated lookup and outer admission
  remain separate premises. It covers the product's released Credit branch;
  it does not add a released Refund branch.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms replay_never_replaces_a_retained_settlement
    matching_rows_compute_the_original_native_credit_commit native_duplicate_value_uses_the_revision_of_the_product_original_credit})
  then () else error "Unexpected oracle in original native settlement correspondence"
\<close>

end
