(* SPDX-License-Identifier: BSD-3-Clause *)
theory Even_Amount_Policy_Boundary
  imports Funding_Realization Funding_Guard_Controls
begin

section \<open>A Property of the Actual Spend-Permission Input\<close>

definition even_amount_spend_policy :: "lock_context \<Rightarrow> bool" where
  "even_amount_spend_policy context \<longleftrightarrow>
    (\<forall>caller key sender recipient amount operation.
      (caller,key,sender,recipient,amount,operation)\<in>lock_spend_permissions context
      \<longrightarrow> even amount)"

definition requested_policy_effect :: "execution_request \<Rightarrow> transfer_binding \<Rightarrow>
  nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> descendant_effect" where
  "requested_policy_effect request root sender recipient amount=
    \<lparr>lineage_root=root,lineage_from=sender,lineage_to=recipient,lineage_amount=amount,
      lineage_operation=binding_operation(request_binding request),lineage_caller=request_caller request,
      lineage_authority_epoch=request_authority_epoch request,lineage_version=request_version request\<rparr>"

lemma successful_descendant_reads_its_exact_spend_permission:
  assumes success: "snd(execute_descendant context request root sender recipient amount machine)=Descendant_Executed"
  shows "(request_caller request,binding_key root,sender,recipient,amount,
      binding_operation(request_binding request))\<in>lock_spend_permissions context"
    "amount\<le>funded_units(machine_state machine)(binding_key root,holder_account root sender)"
  using success
  by (auto simp: execute_descendant_def record_observation_def Let_def split: if_splits)

lemma successful_descendant_has_its_actual_event_state:
  assumes "snd(execute_descendant context request root sender recipient amount machine)=Descendant_Executed"
  shows "machine_state(fst(execute_descendant context request root sender recipient amount machine))=
    apply_reservation_event(Descendant_Event(requested_policy_effect request root sender recipient amount))
      (machine_state machine)"
  using assms
  by (auto simp: execute_descendant_def requested_policy_effect_def record_observation_def
      commit_reservation_event_def Let_def split: if_splits)

lemma rejected_descendant_keeps_its_actual_funding:
  assumes "snd(execute_descendant context request root sender recipient amount machine)\<noteq>Descendant_Executed"
  shows "funded_units(machine_state(fst(execute_descendant context request root sender recipient amount machine)))=
    funded_units(machine_state machine)"
  using assms
  by (auto simp: execute_descendant_def record_observation_def Let_def split: if_splits)

lemma an_even_two_cell_move_preserves_parity:
  fixes funding :: "'cell \<Rightarrow> nat"
  assumes quantity: "even amount" and enough: "amount\<le>funding source"
  shows "even(((funding(source:=funding source-amount))
      (target:=(funding(source:=funding source-amount))target+amount))cell)=even(funding cell)"
proof -
  have withdrawal: "\<And>entry. even((funding(source:=funding source-amount))entry)=even(funding entry)"
    using quantity enough by (auto simp: fun_upd_apply)
  show ?thesis using enough by (simp add: fun_upd_apply quantity withdrawal)
qed

lemma an_even_actual_descendant_event_preserves_funding_parity:
  assumes quantity: "even(lineage_amount effect)"
    and enough: "lineage_amount effect\<le>funded_units state
      (binding_key(lineage_root effect),holder_account(lineage_root effect)(lineage_from effect))"
  shows "even(funded_units(apply_reservation_event(Descendant_Event effect)state)(key,account))=
    even(funded_units state(key,account))"
proof -
  let ?source="(binding_key(lineage_root effect),holder_account(lineage_root effect)(lineage_from effect))"
  let ?target="(binding_key(lineage_root effect),holder_account(lineage_root effect)(lineage_to effect))"
  have move:
    "even((((funded_units state)(?source:=funded_units state ?source-lineage_amount effect))
      (?target:=((funded_units state)(?source:=funded_units state ?source-lineage_amount effect))?target+
        lineage_amount effect))(key,account))=even(funded_units state(key,account))"
    by (rule an_even_two_cell_move_preserves_parity[where funding="funded_units state"
      and source="?source" and target="?target" and amount="lineage_amount effect"
      and cell="(key,account)", OF quantity enough])
  show ?thesis using move by (simp add: Let_def)
qed

theorem actual_even_policy_preserves_every_funding_cell_parity:
  assumes policy: "even_amount_spend_policy context"
  shows "even(funded_units(machine_state(fst(execute_descendant context request root sender recipient amount machine)))
      (key,account))=even(funded_units(machine_state machine)(key,account))"
proof (cases "snd(execute_descendant context request root sender recipient amount machine)=Descendant_Executed")
  case True
  have permission:
    "(request_caller request,binding_key root,sender,recipient,amount,
      binding_operation(request_binding request))\<in>lock_spend_permissions context"
    by (rule successful_descendant_reads_its_exact_spend_permission(1)[OF True])
  have quantity: "even amount"
    using policy permission unfolding even_amount_spend_policy_def by blast
  have enough: "amount\<le>funded_units(machine_state machine)(binding_key root,holder_account root sender)"
    by (rule successful_descendant_reads_its_exact_spend_permission(2)[OF True])
  have event:
    "even(funded_units(apply_reservation_event
        (Descendant_Event(requested_policy_effect request root sender recipient amount))(machine_state machine))
      (key,account))=even(funded_units(machine_state machine)(key,account))"
    by (rule an_even_actual_descendant_event_preserves_funding_parity)
      (simp_all add: requested_policy_effect_def quantity enough)
  show ?thesis by (simp only: successful_descendant_has_its_actual_event_state[OF True] event)
next
  case False
  show ?thesis by (simp only: rejected_descendant_keeps_its_actual_funding[OF False])
qed

text \<open>The conclusion applies to rejected as well as successful requests.
  The policy constrains the amount in the actual permission tuple. Successful
  execution reads that tuple and supplies the subtraction bound. No externally
  supplied success flag or proposed final-state invariant is assumed.\<close>

section \<open>Finite Words with One Fixed Current Context\<close>

fun fixed_descendant_context :: "lock_context \<Rightarrow> reservation_action \<Rightarrow> bool" where
  "fixed_descendant_context expected(Descendant_Action actual request root sender recipient amount)=(actual=expected)"
| "fixed_descendant_context expected _=False"

context source_attestation
begin

lemma fixed_even_policy_step_preserves_funding_parity:
  assumes policy: "even_amount_spend_policy context"
    and fixed: "fixed_descendant_context context action"
  shows "even(funded_units(machine_state(reservation_step balances action machine))(key,account))=
    even(funded_units(machine_state machine)(key,account))"
  using fixed
  by (cases action)
    (auto simp: actual_even_policy_preserves_every_funding_cell_parity[OF policy])

theorem finite_fixed_even_policy_preserves_funding_parity:
  assumes policy: "even_amount_spend_policy context"
    and fixed: "\<forall>action\<in>set actions. fixed_descendant_context context action"
  shows "even(funded_units(machine_state(run_reservations balances actions machine))(key,account))=
    even(funded_units(machine_state machine)(key,account))"
  using fixed
proof (induction actions arbitrary: machine)
  case Nil
  then show ?case by simp
next
  case (Cons action actions)
  have head: "fixed_descendant_context context action" using Cons.prems by simp
  have tail: "\<forall>next\<in>set actions. fixed_descendant_context context next" using Cons.prems by simp
  have one:
    "even(funded_units(machine_state(reservation_step balances action machine))(key,account))=
      even(funded_units(machine_state machine)(key,account))"
    by (rule fixed_even_policy_step_preserves_funding_parity[OF policy head])
  have rest:
    "even(funded_units(machine_state(run_reservations balances actions
        (reservation_step balances action machine)))(key,account))=
      even(funded_units(machine_state(reservation_step balances action machine))(key,account))"
    by (rule Cons.IH[OF tail])
  show ?case by (simp only: run_reservations.simps rest one)
qed

end

section \<open>A Nonempty Bidirectional Policy on a Generated Two-Root Seed\<close>

definition even_boundary_permissions ::
  "(nat \<times> source_key \<times> nat \<times> nat \<times> nat \<times> message_operation) set" where
  "even_boundary_permissions={
    (caller,key,sender,recipient,amount,operation).
      caller=0 \<and> key\<in>{(0,17),(0,23)} \<and> sender\<in>{3,4} \<and> recipient\<in>{3,4} \<and>
      sender\<noteq>recipient \<and> 0<amount \<and> even amount \<and> operation=Ordinary_Transfer_Effect}"

definition even_boundary_context :: lock_context where
  "even_boundary_context=(funding_probe_context(sample_binding 17)4 3 1)\<lparr>
    lock_authority:=(lock_authority(funding_probe_context(sample_binding 17)4 3 1))
      \<lparr>context_permissions:=UNIV\<rparr>,lock_spend_permissions:=even_boundary_permissions\<rparr>"

definition even_boundary_request :: "nat \<Rightarrow> execution_request" where
  "even_boundary_request amount=funding_probe_request(realization_certificates(sample_binding 17))
    (sample_binding 17)3 amount"

abbreviation even_boundary_seed :: reservation_machine where
  "even_boundary_seed \<equiv> core_parent(coupled_core realization_lineage_seed)"

lemma even_boundary_binding_fields [simp]:
  "binding_key(sample_binding 17)=(0,17)"
  "binding_key(sample_binding 23)=(0,23)"
  "binding_destination(sample_binding 17)=2"
  "binding_destination(sample_binding 23)=2"
  "binding_asset(sample_binding 17)=17"
  "binding_asset(sample_binding 23)=17"
  by (simp_all add: sample_binding_def example_binding_def)

lemma even_boundary_request_fields [simp]:
  "request_binding(even_boundary_request amount)=
    descendant_binding(sample_binding 17)3 amount Ordinary_Transfer_Effect"
  "request_caller(even_boundary_request amount)=0"
  by (simp_all add: even_boundary_request_def funding_probe_request_def)

lemma even_boundary_context_spend_field [simp]:
  "lock_spend_permissions even_boundary_context=even_boundary_permissions"
  by (simp add: even_boundary_context_def)

lemma even_boundary_seed_unit_table [simp]:
  "realization_units even_boundary_seed(sample_binding 17)3=0"
  "realization_units even_boundary_seed(sample_binding 17)4=5"
  "realization_units even_boundary_seed(sample_binding 23)3=5"
  "realization_units even_boundary_seed(sample_binding 23)4=0"
  by (simp_all add: realization_units_def holder_account_def realization_seed_funding)

lemma the_fixed_boundary_context_has_an_even_amount_policy:
  "even_amount_spend_policy even_boundary_context"
  by (auto simp: even_amount_spend_policy_def even_boundary_context_def even_boundary_permissions_def)

theorem the_even_policy_is_nonempty_and_bidirectional_for_both_roots:
  "(0,(0,17),3,4,2,Ordinary_Transfer_Effect)\<in>lock_spend_permissions even_boundary_context"
  "(0,(0,17),4,3,2,Ordinary_Transfer_Effect)\<in>lock_spend_permissions even_boundary_context"
  "(0,(0,23),3,4,2,Ordinary_Transfer_Effect)\<in>lock_spend_permissions even_boundary_context"
  "(0,(0,23),4,3,2,Ordinary_Transfer_Effect)\<in>lock_spend_permissions even_boundary_context"
  by (simp_all add: even_boundary_context_def even_boundary_permissions_def)

theorem even_boundary_seed_has_an_actual_joint_source_prefix:
  "even_boundary_seed=core_parent(coupled_core(realized.run_source_coupling
    ((realization_credit_word 17@realization_credit_word 23)@
      source_realization_word(linked_certificate 17)0 realization_seed_effect)
    (initial_source_coupling sample_balances(sample_metadata ACTIVE)conservation_contexts)))"
proof -
  have prefix:
    "realization_source_second=realized.run_source_coupling
      (realization_credit_word 17@realization_credit_word 23)
      (initial_source_coupling sample_balances(sample_metadata ACTIVE)conservation_contexts)"
    by (rule conjunct1[OF realization_two_roots_are_an_actual_joint_prefix])
  show ?thesis by (simp add: realization_lineage_seed_def prefix realized.progress_source_run_append)
qed

lemma even_boundary_seed_has_its_actual_credit:
  "sample_binding 17\<in>set(credit_history(received_messages(machine_state even_boundary_seed)))"
  using realization_exchange_inputs(1) by simp

lemma even_boundary_current_inputs_are_authorized:
  "current_use_allowed(lock_authority even_boundary_context)(even_boundary_request amount)"
  "metadata_permission even_boundary_context(even_boundary_request amount)2"
  "context_endpoint(lock_authority even_boundary_context)=2"
  by (simp_all add: even_boundary_context_def even_boundary_request_def funding_probe_context_def
      funding_probe_request_def current_use_allowed_def metadata_permission_def funding_probe_metadata_def
      sample_binding_def example_binding_def descendant_binding_def get_reg_state_def get_asset_state_def
      ordinary_transfer_allowed_def)

theorem actual_even_boundary_probe_reply:
  "snd(execute_descendant even_boundary_context(even_boundary_request amount)
    (sample_binding 17)4 3 amount even_boundary_seed)=
    (if 0<amount \<and> even amount \<and> amount\<le>5 then Descendant_Executed else Request_Rejected)"
proof -
  note reply=actual_descendant_reply_ignores_redundant_pooled_bound[OF realization_seed_financial,
    where c=even_boundary_context and r="even_boundary_request amount" and root="sample_binding 17"
      and sender=4 and recipient=3 and amount=amount]
  show ?thesis
    by (simp only: reply; auto simp: even_boundary_seed_has_its_actual_credit
        even_boundary_current_inputs_are_authorized even_boundary_permissions_def
        descendant_binding_def holder_account_def realization_seed_funding split: if_splits)
qed

theorem one_unit_is_rejected_but_two_units_really_execute:
  "snd(execute_descendant even_boundary_context(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)=Request_Rejected"
  "snd(execute_descendant even_boundary_context(even_boundary_request 2)
      (sample_binding 17)4 3 2 even_boundary_seed)=Descendant_Executed"
  by (simp_all add: actual_even_boundary_probe_reply)

theorem the_permitted_two_unit_call_changes_actual_funding:
  "funded_units(machine_state(fst(execute_descendant even_boundary_context(even_boundary_request 2)
      (sample_binding 17)4 3 2 even_boundary_seed)))((0,17),(2,17,3))=2"
  "funded_units(machine_state(fst(execute_descendant even_boundary_context(even_boundary_request 2)
      (sample_binding 17)4 3 2 even_boundary_seed)))((0,17),(2,17,4))=3"
proof -
  show "funded_units(machine_state(fst(execute_descendant even_boundary_context(even_boundary_request 2)
      (sample_binding 17)4 3 2 even_boundary_seed)))((0,17),(2,17,3))=2"
    by (simp only: successful_descendant_has_its_actual_event_state
          [OF one_unit_is_rejected_but_two_units_really_execute(2)];
        simp add: requested_policy_effect_def even_boundary_request_def funding_probe_request_def
          sample_binding_def example_binding_def holder_account_def realization_seed_funding Let_def)
  show "funded_units(machine_state(fst(execute_descendant even_boundary_context(even_boundary_request 2)
      (sample_binding 17)4 3 2 even_boundary_seed)))((0,17),(2,17,4))=3"
    by (simp only: successful_descendant_has_its_actual_event_state
          [OF one_unit_is_rejected_but_two_units_really_execute(2)];
        simp add: requested_policy_effect_def even_boundary_request_def funding_probe_request_def
          sample_binding_def example_binding_def holder_account_def realization_seed_funding Let_def)
qed

section \<open>Equal Margins Do Not Eliminate the Actual Policy Obstruction\<close>

definition even_boundary_target :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat" where
  "even_boundary_target root holder=
    (if binding_key root=(0,17) then (if holder=3 then 1 else if holder=4 then 4 else 0)
     else if binding_key root=(0,23) then (if holder=3 then 4 else if holder=4 then 1 else 0)
     else 0)"

theorem the_parity_obstructed_target_has_the_same_rows_and_actual_columns:
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23].
    sum_list(map(even_boundary_target root)[3,4])=
      sum_list(map(realization_units even_boundary_seed root)[3,4])"
  "\<forall>account. realization_account_total [sample_binding 17,sample_binding 23][3,4]
      even_boundary_target account=
    realization_account_total [sample_binding 17,sample_binding 23][3,4]
      (realization_units even_boundary_seed) account"
  by (auto simp: even_boundary_target_def realization_account_total_def
      holder_account_def split: if_splits)

theorem no_actual_finite_word_with_the_fixed_even_policy_realizes_the_target:
  assumes fixed: "\<forall>action\<in>set actions. fixed_descendant_context even_boundary_context action"
  shows "\<not>(\<forall>root\<in>set[sample_binding 17,sample_binding 23]. \<forall>holder\<in>set[3,4].
    realization_units(realized.run_reservations sample_balances actions even_boundary_seed)root holder=
      even_boundary_target root holder)"
proof
  assume target: "\<forall>root\<in>set[sample_binding 17,sample_binding 23]. \<forall>holder\<in>set[3,4].
    realization_units(realized.run_reservations sample_balances actions even_boundary_seed)root holder=
      even_boundary_target root holder"
  have parity:
    "even(funded_units(machine_state(realized.run_reservations sample_balances actions even_boundary_seed))
      ((0,17),(2,17,3)))=even(funded_units(machine_state even_boundary_seed)((0,17),(2,17,3)))"
    by (rule realized.finite_fixed_even_policy_preserves_funding_parity
      [OF the_fixed_boundary_context_has_an_even_amount_policy fixed])
  have unit:
    "funded_units(machine_state(realized.run_reservations sample_balances actions even_boundary_seed))
      ((0,17),(2,17,3))=1"
    using target
    by (auto simp: realization_units_def even_boundary_target_def holder_account_def)
  show False using parity by (simp add: unit realization_seed_funding)
qed

section \<open>The Existing Single-Guard Mutant Removes This Obstruction\<close>

lemma even_boundary_mutant_is_the_actual_granted_probe:
  "execute_without_exact_spend_guard even_boundary_context(even_boundary_request amount)
      (sample_binding 17)4 3 amount machine=
    execute_descendant(funding_probe_context(sample_binding 17)4 3 amount)(even_boundary_request amount)
      (sample_binding 17)4 3 amount machine"
  by (simp add: execute_without_exact_spend_guard_def execute_descendant_def Let_def
      even_boundary_context_def even_boundary_request_def funding_probe_context_def funding_probe_request_def
      metadata_permission_def current_use_allowed_def funding_probe_metadata_def descendant_binding_def
      sample_binding_def example_binding_def get_reg_state_def get_asset_state_def ordinary_transfer_allowed_def)

theorem removing_the_exact_spend_guard_admits_the_forbidden_one_unit:
  "snd(execute_descendant even_boundary_context(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)=Request_Rejected"
  "snd(execute_without_exact_spend_guard even_boundary_context(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)=Descendant_Executed"
proof -
  show "snd(execute_descendant even_boundary_context(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)=Request_Rejected"
    by (rule one_unit_is_rejected_but_two_units_really_execute(1))
  have actual:
    "snd(execute_descendant(funding_probe_context(sample_binding 17)4 3 1)(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)=Descendant_Executed"
    unfolding even_boundary_request_def
    by (simp only: actual_probe_reply_is_the_funding_threshold
        [OF realization_seed_financial even_boundary_seed_has_its_actual_credit];
      simp add: holder_account_def realization_seed_funding)
  show "snd(execute_without_exact_spend_guard even_boundary_context(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)=Descendant_Executed"
    by (simp only: even_boundary_mutant_is_the_actual_granted_probe actual)
qed

theorem the_same_guard_removal_changes_the_actual_cell_parity:
  "funded_units(machine_state(fst(execute_without_exact_spend_guard even_boundary_context(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)))((0,17),(2,17,3))=1"
proof -
  have success:
    "snd(execute_descendant(funding_probe_context(sample_binding 17)4 3 1)(even_boundary_request 1)
      (sample_binding 17)4 3 1 even_boundary_seed)=Descendant_Executed"
    using removing_the_exact_spend_guard_admits_the_forbidden_one_unit(2)
    by (simp only: even_boundary_mutant_is_the_actual_granted_probe)
  show ?thesis
    by (simp only: even_boundary_mutant_is_the_actual_granted_probe
        successful_descendant_has_its_actual_event_state[OF success];
      simp add: requested_policy_effect_def even_boundary_request_def funding_probe_request_def
        sample_binding_def example_binding_def holder_account_def realization_seed_funding Let_def)
qed

text \<open>The initial table is [[0,5],[5,0]] in root order 17,23 and holder
  order 3,4. The target [[1,4],[4,1]] has the same root totals and the same
  complete destination-account totals. The fixed permission set contains
  positive even transfers in both directions for both roots, and an actual
  two-unit request succeeds. Nevertheless, every finite descendant word using
  that fixed context preserves every funding cell's parity. The target changes
  parity and is therefore outside this execution image.

  The negative control reuses the existing exact-spend-guard mutant. It leaves
  the initial state, current authority, metadata, root and pooled funding,
  request, and remaining guards unchanged. The one-unit request rejected by
  the original consumer then executes and changes the cell from zero to one.

  This result does not contradict the constructive realization factory, which
  supplies a permitted current context for each chosen move. It establishes
  a boundary for fixed amount-sensitive permissions, not a new trust service,
  an implementation refinement, or a restriction of product support.\<close>

section \<open>The Two Forbidden Unit Moves Realize the Complete Target\<close>

definition even_boundary_first_mutant :: "reservation_machine \<times> reservation_reply" where
  "even_boundary_first_mutant=execute_without_exact_spend_guard even_boundary_context(even_boundary_request 1)
    (sample_binding 17)4 3 1 even_boundary_seed"

definition even_boundary_second_request :: execution_request where
  "even_boundary_second_request=funding_probe_request(realization_certificates(sample_binding 23))
    (sample_binding 23)4 1"

definition even_boundary_second_mutant :: "reservation_machine \<times> reservation_reply" where
  "even_boundary_second_mutant=execute_without_exact_spend_guard even_boundary_context even_boundary_second_request
    (sample_binding 23)3 4 1(fst even_boundary_first_mutant)"

lemma even_boundary_first_mutant_is_the_granted_realization:
  "even_boundary_first_mutant=realization_result realization_certificates
    (realization_effect(sample_binding 17)4 3 1)even_boundary_seed"
  by (simp only: even_boundary_first_mutant_def even_boundary_mutant_is_the_actual_granted_probe;
    simp add: realization_result_def realization_effect_def even_boundary_request_def)

lemma even_boundary_first_granted_realization_succeeds:
  "snd(realization_result realization_certificates
    (realization_effect(sample_binding 17)4 3 1)even_boundary_seed)=Descendant_Executed"
  using removing_the_exact_spend_guard_admits_the_forbidden_one_unit(2)
  by (simp only: even_boundary_first_mutant_def[symmetric]
      even_boundary_first_mutant_is_the_granted_realization)

lemma even_boundary_second_mutant_is_the_granted_realization:
  "execute_without_exact_spend_guard even_boundary_context even_boundary_second_request
      (sample_binding 23)3 4 1 machine=
    realization_result realization_certificates(realization_effect(sample_binding 23)3 4 1)machine"
  by (simp add: execute_without_exact_spend_guard_def execute_descendant_def realization_result_def
      realization_effect_def even_boundary_context_def even_boundary_second_request_def funding_probe_context_def
      funding_probe_request_def metadata_permission_def current_use_allowed_def funding_probe_metadata_def
      descendant_binding_def sample_binding_def example_binding_def get_reg_state_def get_asset_state_def
      ordinary_transfer_allowed_def Let_def)

lemma even_boundary_second_granted_realization_succeeds:
  "snd(realization_result realization_certificates(realization_effect(sample_binding 23)3 4 1)
    (fst even_boundary_first_mutant))=Descendant_Executed"
proof -
  have financial: "financial_history_agreement sample_balances(fst even_boundary_first_mutant)"
    unfolding even_boundary_first_mutant_is_the_granted_realization
    by (rule realization_result_financial[OF realization_seed_financial
      even_boundary_first_granted_realization_succeeds])
  have credited: "sample_binding 23\<in>set(credit_history(received_messages
      (machine_state(fst even_boundary_first_mutant))))"
    using realization_exchange_inputs(1)
    by (simp add: even_boundary_first_mutant_is_the_granted_realization)
  have frame: "funded_units(machine_state(fst even_boundary_first_mutant))((0,23),(2,17,3))=
      funded_units(machine_state even_boundary_seed)((0,23),(2,17,3))"
    unfolding even_boundary_first_mutant_is_the_granted_realization
    by (rule realization_result_funding_frame) (simp add: realization_effect_def)
  have funded: "funded_units(machine_state(fst even_boundary_first_mutant))((0,23),(2,17,3))=5"
    by (simp only: frame realization_seed_funding)
  note reply=actual_probe_reply_is_the_funding_threshold[OF financial credited,
    where sender=3 and recipient=4 and amount=1 and certificate="realization_certificates(sample_binding 23)"]
  show ?thesis
    by (simp del: One_nat_def add: realization_result_def realization_effect_def reply holder_account_def funded)
qed

theorem both_forbidden_unit_moves_execute_under_the_same_single_guard_removal:
  "snd even_boundary_first_mutant=Descendant_Executed"
  "snd even_boundary_second_mutant=Descendant_Executed"
proof -
  show "snd even_boundary_first_mutant=Descendant_Executed"
    by (simp only: even_boundary_first_mutant_is_the_granted_realization
        even_boundary_first_granted_realization_succeeds)
  show "snd even_boundary_second_mutant=Descendant_Executed"
    by (simp only: even_boundary_second_mutant_def even_boundary_second_mutant_is_the_granted_realization
        even_boundary_second_granted_realization_succeeds)
qed

theorem the_original_policy_rejects_the_second_unit_move_too:
  "snd(execute_descendant even_boundary_context even_boundary_second_request
    (sample_binding 23)3 4 1(fst even_boundary_first_mutant))=Request_Rejected"
  by (simp add: execute_descendant_def even_boundary_permissions_def even_boundary_second_request_def
      funding_probe_request_def descendant_binding_def record_observation_def Let_def)

lemma even_boundary_granted_event_state:
  assumes "snd(realization_result certificates(realization_effect root sender recipient amount)machine)=Descendant_Executed"
  shows "machine_state(fst(realization_result certificates(realization_effect root sender recipient amount)machine))=
    apply_reservation_event(Descendant_Event(realization_effect root sender recipient amount))(machine_state machine)"
  by (simp only: realization_result_commits[OF assms];
    simp add: record_observation_def commit_reservation_event_def realization_effect_def)

lemma even_boundary_two_mutants_have_the_exact_event_state:
  "machine_state(fst even_boundary_second_mutant)=
    apply_reservation_event(Descendant_Event(realization_effect(sample_binding 23)3 4 1))
      (apply_reservation_event(Descendant_Event(realization_effect(sample_binding 17)4 3 1))
        (machine_state even_boundary_seed))"
proof -
  have first: "machine_state(fst even_boundary_first_mutant)=
      apply_reservation_event(Descendant_Event(realization_effect(sample_binding 17)4 3 1))
        (machine_state even_boundary_seed)"
    unfolding even_boundary_first_mutant_is_the_granted_realization
    by (rule even_boundary_granted_event_state[OF even_boundary_first_granted_realization_succeeds])
  have second: "machine_state(fst even_boundary_second_mutant)=
      apply_reservation_event(Descendant_Event(realization_effect(sample_binding 23)3 4 1))
        (machine_state(fst even_boundary_first_mutant))"
    unfolding even_boundary_second_mutant_def even_boundary_second_mutant_is_the_granted_realization
    by (rule even_boundary_granted_event_state[OF even_boundary_second_granted_realization_succeeds])
  show ?thesis by (simp only: second first)
qed

theorem the_two_actual_mutant_moves_realize_the_parity_obstructed_table:
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23]. \<forall>holder\<in>set[3,4].
    realization_units(fst even_boundary_second_mutant)root holder=even_boundary_target root holder"
  by (simp add: realization_units_def even_boundary_two_mutants_have_the_exact_event_state
      realization_effect_def even_boundary_target_def holder_account_def realization_seed_funding Let_def)

theorem the_two_actual_mutant_moves_restore_pooled_balances:
  "destination_units(machine_state(fst even_boundary_second_mutant))=destination_units(machine_state even_boundary_seed)"
  by (rule ext)
    (auto simp: even_boundary_two_mutants_have_the_exact_event_state realization_effect_def
      holder_account_def realization_seed_funding Let_def split: if_splits)

theorem the_two_actual_mutant_moves_do_not_create_source_effects_or_credits:
  "source_units(machine_state(fst even_boundary_second_mutant))=source_units(machine_state even_boundary_seed)"
  "source_effects(machine_state(fst even_boundary_second_mutant))=source_effects(machine_state even_boundary_seed)"
  "received_messages(machine_state(fst even_boundary_second_mutant))=received_messages(machine_state even_boundary_seed)"
  by (simp_all add: even_boundary_two_mutants_have_the_exact_event_state Let_def)

text \<open>Both calls use the identical fixed even-amount context. Only the
  exact-spend membership check is absent. The first move takes one unit of root
  17 from holder 4 to holder 3; the second takes one unit of root 23 from holder
  3 to holder 4. Their actual replies are derived before the final table, which
  is exactly [[1,4],[4,1]]. Pooled balances and the source/credit state are unchanged.\<close>

end
