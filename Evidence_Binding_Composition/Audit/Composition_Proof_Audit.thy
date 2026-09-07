(* SPDX-License-Identifier: BSD-3-Clause *)
theory Composition_Proof_Audit
  imports Composition_Audit_Base
    "Evidence_Binding_Composition.Funding_Realization"
    "Evidence_Binding_Composition.Funding_Characterization"
    "Evidence_Binding_Composition.Source_Realization_Link"
    "Evidence_Binding_Composition.Funding_Guard_Controls"
    "Evidence_Binding_Composition.Historical_Decision_Projection"
    "Evidence_Binding_Composition.Integration_Boundaries"
    "Evidence_Binding_Composition.Integration_Transport"
    "Evidence_Binding_Composition.Integration_Examples"
    "Evidence_Binding_Composition.Historical_Reachability_Boundary"
    "Evidence_Binding_Composition.Source_Call_Realization"
    "Evidence_Binding_Composition.Regulatory_Composition_Example"
    "Evidence_Binding_Composition.Funding_Order_Boundary"
    "Evidence_Binding_Composition.Funding_Completion_Separation"
    "Evidence_Binding_Composition.Even_Amount_Policy_Boundary"
begin

ML \<open>
val _ = let
val audited_theory = @{theory};
val parent_theory = @{theory Composition_Audit_Base};
val audit_context = @{context};
val audit_dir = Resources.master_directory audited_theory;
val audit_progress = Path.append audit_dir (Path.basic "audit-progress.txt");
val _ = File.write audit_progress "started\n";
fun audit_stage stage = File.write audit_progress (stage ^ "\n");
fun audit_flat value = String.translate
  (fn #"\n" => " " | #"\r" => " " | #"\t" => " " | c => String.str c)
  (XML.content_of (YXML.parse_body value));
fun audit_write name lines = File.write (Path.append audit_dir (Path.basic name))
  (cat_lines lines ^ "\n");
val audited_roots = [
  ("finite-realization", @{thm source_attestation.finite_funding_realization}),
  ("finite-characterization", @{thm source_attestation.finite_funding_admissibility_iff_realization}),
  ("execution-forces-margins", @{thm actual_successful_image_forces_admissibility}),
  ("realization-source-frame", @{thm source_attestation.characterized_image_has_actual_parent_execution_and_source_frame}),
  ("actual-source-step", @{thm source_attestation.source_realization_one_step_is_the_actual_parent_result}),
  ("actual-source-plan", @{thm source_attestation.source_realization_constructive_plan_uses_the_actual_dispatcher}),
  ("actual-source-word", @{thm source_attestation.source_realization_finite_word_projection}),
  ("actual-two-source-roots", @{thm realization_two_roots_are_an_actual_joint_prefix}),
  ("actual-two-root-consumers", @{thm realization_two_roots_supply_the_actual_consumers}),
  ("actual-two-root-dispatch", @{thm actual_two_root_plan_activates_every_source_dispatch}),
  ("actual-source-erasure", @{thm actual_source_realization_preserves_erased_state_and_source_pool}),
  ("actual-source-event-frame", @{thm actual_realization_has_no_new_source_credit_or_return}),
  ("observed-callback", @{thm source_attestation.observed_callback_history_projection}),
  ("sourced-callback", @{thm source_attestation.sourced_callback_history_projection}),
  ("observed-finite-word", @{thm source_attestation.every_observed_call_word_has_the_same_decisions}),
  ("sourced-finite-word", @{thm source_attestation.every_sourced_call_word_has_the_same_decisions}),
  ("sourced-completions-1", @{thm source_attestation.sourced_finite_completions_and_history(1)}),
  ("sourced-completions-2", @{thm source_attestation.sourced_finite_completions_and_history(2)}),
  ("sourced-completions-3", @{thm source_attestation.sourced_finite_completions_and_history(3)}),
  ("current-information-iff", @{thm source_attestation.current_snapshot_equality_iff_all_actual_cache_probes}),
  ("raw-journal-iff", @{thm source_attestation.actual_raw_journal_equality_iff}),
  ("raw-source-iff", @{thm source_attestation.actual_source_effect_probe_equality_iff}),
  ("recovery-information-iff", @{thm durable_call_protocol.current_replay_evidence_equality_iff_all_candidate_admissions}),
  ("recovered-dispatch-iff", @{thm durable_call_protocol.actual_recovered_dispatch_admission_is_exact}),
  ("block-decoder", @{thm recovery_block_encoding_has_an_actual_decoder}),
  ("block-recovery", @{thm durable_call_protocol.a_complete_ordered_partition_recovers_the_actual_source}),
  ("block-order-negative", @{thm durable_call_protocol.changed_block_order_is_rejected_by_the_actual_recovery_check}),
  ("recovery-word-transport", @{thm operational_call_projection.restored_runtime_transports_every_future_call_word}),
  ("recovery-completions-1", @{thm operational_call_projection.restored_runtime_preserves_all_future_completed_replies(1)}),
  ("recovery-completions-2", @{thm operational_call_projection.restored_runtime_preserves_all_future_completed_replies(2)}),
  ("ordered-composition", @{thm operational_call_projection.ordered_call_composition_commutes_with_projection}),
  ("ordered-recovery-completions", @{thm operational_call_projection.recovered_ordered_blocks_transport_finite_completed_calls}),
  ("nonidentity-history", @{thm actual_history_projection_changes_a_generated_payload}),
  ("current-distinction", @{thm the_actual_current_probe_keeps_the_clock_distinction}),
  ("current-guard-removal", @{thm removing_the_current_cache_guard_changes_the_actual_probe_reply}),
  ("original-reachability-invariant", @{thm source_attestation.every_generated_call_authority_keeps_current_capture}),
  ("projection-not-original-reachable", @{thm projected_actual_history_is_not_any_original_call_authority}),
  ("reachability-reply-separation", @{thm original_reachability_and_reply_preservation_are_distinct}),
  ("spend-guard-removal", @{thm exact_spend_removal_changes_a_source_generated_execution}),
  ("actual-source-call-translation", @{thm source_attestation.translated_finite_word_has_the_exact_joint_source}),
  ("actual-completed-source-cut", @{thm source_attestation.every_translated_client_cut_has_its_actual_completed_reply}),
  ("generated-source-recovery", @{thm source_attestation.generated_translation_has_exact_current_recovery}),
  ("generated-source-recovery-transport", @{thm source_attestation.generated_translation_transports_recovery_and_future_replies(1)}),
  ("actual-durable-funding", @{thm actual_durable_calls_have_the_constructed_funding}),
  ("actual-source-to-completion", @{thm actual_two_root_source_to_completed_descendant_reply}),
  ("actual-source-completion-after-recovery", @{thm recovered_value_flow_retains_its_completed_descendant}),
  ("equal-pool-completed-distinction", @{thm pooled_balances_do_not_determine_the_actual_fresh_completed_probe}),
  ("recovered-funding-success", @{thm recovery_and_projection_preserve_the_actual_funding_separation(1)}),
  ("recovered-funding-refusal", @{thm recovery_and_projection_preserve_the_actual_funding_separation(2)}),
  ("regulatory-policy-distinction", @{thm equal_funding_does_not_supply_the_current_active_policy}),
  ("actual-regulatory-call-prefix", @{thm actual_observed_calls_generate_the_previously_required_cut}),
  ("actual-regulatory-enforcement", @{thm the_same_call_machine_completes_actual_enforcement}),
  ("regulatory-projection-nonidentity", @{thm actual_generated_regulatory_history_is_changed_by_projection}),
  ("recovered-regulatory-refusal", @{thm both_regulatory_decisions_survive_recovery_projection_and_future_calls(1)}),
  ("recovered-regulatory-enforcement", @{thm both_regulatory_decisions_survive_recovery_projection_and_future_calls(2)}),
  ("ordered-word-reflection", @{thm successful_canonical_journals_reflect_the_whole_word}),
  ("reverse-actual-word", @{thm reverse_exchange_activates_every_actual_source_consumer}),
  ("equal-selected-funding", @{thm the_two_orders_have_the_same_selected_funding}),
  ("actual-raw-order-distinction", @{thm the_two_successful_orders_have_different_actual_raw_replies}),
  ("actual-even-step-invariant", @{thm actual_even_policy_preserves_every_funding_cell_parity}),
  ("actual-even-word-invariant", @{thm source_attestation.finite_fixed_even_policy_preserves_funding_parity}),
  ("nonempty-even-policy", @{thm the_even_policy_is_nonempty_and_bidirectional_for_both_roots(1)}),
  ("even-policy-actual-success", @{thm one_unit_is_rejected_but_two_units_really_execute(2)}),
  ("fixed-even-policy-no-go", @{thm no_actual_finite_word_with_the_fixed_even_policy_realizes_the_target}),
  ("even-policy-guard-removal", @{thm the_same_guard_removal_changes_the_actual_cell_parity}),
  ("two-forbidden-moves-complete", @{thm both_forbidden_unit_moves_execute_under_the_same_single_guard_removal(2)}),
  ("full-policy-counter-target", @{thm the_two_actual_mutant_moves_realize_the_parity_obstructed_table}),
  ("full-policy-counter-pooled-frame", @{thm the_two_actual_mutant_moves_restore_pooled_balances}),
  ("even-target-rows", @{thm the_parity_obstructed_target_has_the_same_rows_and_actual_columns(1)}),
  ("even-target-actual-columns", @{thm the_parity_obstructed_target_has_the_same_rows_and_actual_columns(2)}),
  ("even-second-original-refusal", @{thm the_original_policy_rejects_the_second_unit_move_too}),
  ("even-mutant-source-units-frame", @{thm the_two_actual_mutant_moves_do_not_create_source_effects_or_credits(1)}),
  ("even-mutant-source-effects-frame", @{thm the_two_actual_mutant_moves_do_not_create_source_effects_or_credits(2)}),
  ("even-mutant-credit-frame", @{thm the_two_actual_mutant_moves_do_not_create_source_effects_or_credits(3)}),
  ("even-bidirectional-policy-2", @{thm the_even_policy_is_nonempty_and_bidirectional_for_both_roots(2)}),
  ("even-bidirectional-policy-3", @{thm the_even_policy_is_nonempty_and_bidirectional_for_both_roots(3)}),
  ("even-bidirectional-policy-4", @{thm the_even_policy_is_nonempty_and_bidirectional_for_both_roots(4)}),
  ("same-revision-distinct-inputs", @{thm distinct_clock_inputs_have_the_same_revision}),
  ("empty-roots-arithmetic", @{thm empty_roots_are_admissible}),
  ("empty-holders-arithmetic", @{thm empty_holders_are_admissible}),
  ("empty-roots-execution", @{thm empty_roots_have_the_empty_actual_image}),
  ("empty-holders-execution", @{thm empty_holders_have_the_empty_actual_image}),
  ("seed-probe-fresh", @{thm the_two_probe_identifiers_are_fresh_at_their_own_cuts(1)}),
  ("exchange-probe-fresh", @{thm the_two_probe_identifiers_are_fresh_at_their_own_cuts(2)}),
  ("probe-identifier-prefix-length", @{thm probe_identifier_difference_records_only_the_extra_prefix}),
  ("each-probe-exact-recovery", @{thm each_generated_probe_has_exact_current_recovery}),
  ("each-recovery-same-machine", @{thm each_recovery_keeps_the_original_generated_machine(1)}),
  ("each-recovery-actual-replica", @{thm each_recovery_keeps_the_original_generated_machine(2)}),
  ("finite-source-financial-frame", @{thm source_attestation.finite_source_realization_preserves_the_exact_financial_projection})
];
fun audit_root (label, theorem) =
  let val oracle_count = length (Thm_Deps.all_oracles [theorem])
  in space_implode "\t" [label, Thm_Name.print (Thm.derivation_name theorem),
    string_of_int oracle_count, string_of_int (Thm.nprems_of theorem),
    audit_flat (Syntax.string_of_term audit_context (Thm.prop_of theorem))] end;
val _ = audit_stage "claims";
val _ = audit_write "claim-roots.tsv"
  ("label\ttheorem\toracles\tpremises\tstatement" :: map audit_root audited_roots);
val _ = audit_stage "combined-oracles";
val _ = if null (Thm_Deps.all_oracles (map #2 audited_roots)) then ()
  else error "Claim roots have oracle dependencies";
val _ = audit_stage "local-facts";
val local_facts = Facts.dest_static true [Global_Theory.facts_of parent_theory]
  (Global_Theory.facts_of audited_theory);
val _ = audit_stage "local-theorems";
val local_thms = map (Global_Theory.transfer_theories audited_theory)
  (maps (fn (_, theorems) => theorems) local_facts);
val local_oracles = Thm_Deps.all_oracles local_thms;
val _ = audit_write "all-local-oracles.txt" [string_of_int (length local_oracles)];
val _ = if null local_oracles then () else error "Local facts have oracle dependencies";

val _ = audit_stage "dependencies";
val _ = audit_write "local-fact-inventory.tsv"
  ("fact\ttheorems" :: map (fn (name, thms) => name ^ "\t" ^
    string_of_int (length thms)) local_facts);
val dependency_rows = Unsynchronized.ref 0;
val theorem_rows = Unsynchronized.ref 0;
val _ = File_Stream.open_output (fn output =>
  File_Stream.open_output (fn inventory =>
    let
      val _ = File_Stream.output output "theorem\tdependency\n";
      val _ = File_Stream.output inventory "fact\tindex\ttheorem\tdirect_dependencies\n";
      fun process (fact, thms) = List.app (fn (index, original) =>
        let
          val _ = audit_stage ("dependency theorem " ^ fact ^ "(" ^ string_of_int (index+1) ^ ")");
          val theorem = Global_Theory.transfer_theories audited_theory original;
          val name = Thm_Name.print (Thm.derivation_name theorem);
          val deps = Thm_Deps.thm_deps audited_theory [theorem];
          val edges = if name = "" then [] else sort_distinct string_ord
            (map (fn (_, dep) => name ^ "\t" ^ Thm_Name.print dep) deps);
          val _ = List.app (fn edge => File_Stream.output output (edge ^ "\n")) edges;
          val _ = File_Stream.output inventory (space_implode "\t"
            [fact, string_of_int (index+1), name, string_of_int (length deps)] ^ "\n");
          val _ = dependency_rows := !dependency_rows + length edges;
          val _ = theorem_rows := !theorem_rows + 1;
        in () end) (map_index I thms);
    in List.app process local_facts end)
    (Path.append audit_dir (Path.basic "local-theorem-inventory.tsv")))
  (Path.append audit_dir (Path.basic "theorem-dependencies-raw.tsv"));
val _ = audit_stage ("dependencies complete: " ^ string_of_int (!theorem_rows) ^
  " theorem entries, " ^ string_of_int (!dependency_rows) ^ " edge rows");
val _ = audit_stage "axioms";
val old_axioms = map #1 (Theory.all_axioms_of parent_theory);
val new_axioms = filter (fn (name, _) => not (member (op =) old_axioms name))
  (Theory.all_axioms_of audited_theory);
val _ = audit_write "introduced-axioms.tsv"
  ("name\tproposition" :: map (fn (name, prop) => name ^ "\t" ^
     audit_flat (Syntax.string_of_term audit_context prop)) new_axioms);
val _ = audit_stage "constants";
val old_constants = map #1 (#constants (Consts.dest (Sign.consts_of parent_theory)));
val new_constants = filter (fn (name, _) => not (member (op =) old_constants name))
  (#constants (Consts.dest (Sign.consts_of audited_theory)));
val _ = audit_write "introduced-constants.tsv"
  ("name\ttype" :: map (fn (name, (typ, _)) => name ^ "\t" ^
    audit_flat (Syntax.string_of_typ audit_context typ)) new_constants);
fun audit_simp_names thy = map (Thm_Name.print o #1)
  (Raw_Simplifier.dest_simps (Simplifier.simpset_of (Proof_Context.init_global thy)));
val _ = audit_stage "simp-rules";
val old_simps = audit_simp_names parent_theory;
val new_simps = filter (fn name => not (member (op =) old_simps name)) (audit_simp_names audited_theory);
val _ = audit_write "introduced-simp-rules.txt" (sort_distinct string_ord new_simps);
val _ = audit_stage "unused";
val unused = Thm_Deps.unused_thms_cmd ([parent_theory],
  [@{theory Funding_Realization}, @{theory Funding_Characterization}, @{theory Source_Realization_Link}, @{theory Funding_Guard_Controls}, @{theory Historical_Decision_Projection}, @{theory Integration_Boundaries}, @{theory Integration_Transport}, @{theory Integration_Examples}, @{theory Historical_Reachability_Boundary}, @{theory Source_Call_Realization}, @{theory Regulatory_Composition_Example}, @{theory Funding_Order_Boundary}, @{theory Funding_Completion_Separation}, @{theory Even_Amount_Policy_Boundary}]);
val _ = audit_write "unused-theorems.txt" (map (Thm_Name.print o #1) unused);
val _ = audit_stage "summary";
val _ = audit_write "audit-summary.txt"
  ["claim_roots=" ^ string_of_int (length audited_roots), "oracle_dependencies=0",
   "introduced_axioms=" ^ string_of_int (length new_axioms),
   "introduced_constants=" ^ string_of_int (length new_constants),
   "introduced_simp_rules=" ^ string_of_int (length new_simps),
   "unused_named_theorems=" ^ string_of_int (length unused)];
val _ = audit_stage "complete";
in () end
\<close>

end
