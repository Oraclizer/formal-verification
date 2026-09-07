(* SPDX-License-Identifier: BSD-3-Clause *)
theory Funding_Order_Boundary
  imports Source_Realization_Link Integration_Boundaries
begin

section \<open>The Raw Reader Reflects Successful Canonical Words\<close>

theorem successful_canonical_journals_reflect_the_whole_word:
  assumes first: "realization_succeeds certificates first initial"
    and second: "realization_succeeds certificates second initial"
    and canonical_first: "\<forall>e\<in>set first. canonical_realization_effect e"
    and canonical_second: "\<forall>e\<in>set second. canonical_realization_effect e"
  shows "machine_journal(run_realization certificates first initial)=
      machine_journal(run_realization certificates second initial) \<longleftrightarrow> first=second"
proof -
  have left: "machine_journal(run_realization certificates first initial)=
    machine_journal initial@map Descendant_Event first"
    by (rule conjunct1[OF run_realization_exact_history[OF first canonical_first]])
  have right: "machine_journal(run_realization certificates second initial)=
    machine_journal initial@map Descendant_Event second"
    by (rule conjunct1[OF run_realization_exact_history[OF second canonical_second]])
  have injective: "inj Descendant_Event" by (rule injI) simp
  show ?thesis by (simp add: left right inj_map_eq_map[OF injective])
qed

definition reverse_exchange_effects :: "descendant_effect list" where
  "reverse_exchange_effects=rev realization_exchange_effects"

definition reverse_exchange_source :: source_coupling_state where
  "reverse_exchange_source=realized.run_source_coupling
    (source_realization_words realization_certificates(\<lambda>_.0)reverse_exchange_effects)realization_lineage_seed"

lemma reverse_exchange_is_also_a_constructed_plan:
  "realization_plan [sample_binding 23,sample_binding 17][3,4]
      (core_parent(coupled_core realization_lineage_seed))realization_exchange_target=reverse_exchange_effects"
  by (simp add: realization_plan_def realization_plan_from_def realization_drain_def
      realization_distribute_def realization_move_def realization_units_def realization_seed_funding
      realization_exchange_target_def realization_exchange_effects_def reverse_exchange_effects_def
      sample_binding_def example_binding_def holder_account_def)

lemma reverse_exchange_inputs:
  "\<forall>root\<in>set[sample_binding 23,sample_binding 17].
    root\<in>set(credit_history(received_messages(machine_state(core_parent(coupled_core realization_lineage_seed)))))"
  "distinct(map binding_key[sample_binding 23,sample_binding 17])"
  "distinct[3::nat,4]"
  "\<forall>root\<in>set[sample_binding 23,sample_binding 17].
    sum_list(map(realization_exchange_target root)[3,4])=
    sum_list(map(realization_units(core_parent(coupled_core realization_lineage_seed))root)[3,4])"
  "\<forall>root\<in>set[sample_binding 23,sample_binding 17].
    record_reference(coupled_core realization_lineage_seed)0 root Confirmed_Decision\<noteq>None"
  "\<forall>root\<in>set[sample_binding 23,sample_binding 17].
    binding_key root\<in>core_published(coupled_core realization_lineage_seed)"
  "\<forall>root\<in>set[sample_binding 23,sample_binding 17].
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_lineage_seed)))
      (binding_destination root)(binding_asset root)=Some ACTIVE"
  using realization_exchange_inputs by auto

theorem reverse_exchange_activates_every_actual_source_consumer:
  "(\<forall>root\<in>set[sample_binding 23,sample_binding 17]. \<forall>holder\<in>set[3,4].
      realization_units(core_parent(coupled_core reverse_exchange_source))root holder=
        realization_exchange_target root holder) \<and>
    coupled_source reverse_exchange_source=coupled_source realization_lineage_seed \<and>
    (\<forall>i<length reverse_exchange_effects.
      realized.source_realization_reply realization_certificates(\<lambda>_.0)(reverse_exchange_effects!i)
        (realized.run_source_coupling(source_realization_words realization_certificates(\<lambda>_.0)
          (take i reverse_exchange_effects))realization_lineage_seed)=
        Coupling_Client_Reply(Protocol_Response Descendant_Executed))"
  using realized.source_realization_constructive_plan_uses_the_actual_dispatcher
    [OF realization_seed_financial reverse_exchange_inputs(1,2,3,4,5,6,7),
      where certificates=realization_certificates]
  by (simp add: reverse_exchange_is_also_a_constructed_plan reverse_exchange_source_def)

lemma reverse_exchange_parent_projection:
  "core_parent(coupled_core reverse_exchange_source)=
    run_realization realization_certificates reverse_exchange_effects
      (core_parent(coupled_core realization_lineage_seed))"
proof -
  have references: "\<forall>e\<in>set reverse_exchange_effects.
    record_reference(coupled_core realization_lineage_seed)0(lineage_root e)Confirmed_Decision\<noteq>None"
    using realization_exchange_inputs(5)
    by (simp add: reverse_exchange_effects_def realization_exchange_effects_def realization_effect_def)
  have published: "\<forall>e\<in>set reverse_exchange_effects.
    binding_key(lineage_root e)\<in>core_published(coupled_core realization_lineage_seed)"
    using realization_exchange_inputs(6)
    by (simp add: reverse_exchange_effects_def realization_exchange_effects_def realization_effect_def)
  have active: "\<forall>e\<in>set reverse_exchange_effects.
    get_reg_state(receiver_snapshot(core_regulatory(coupled_core realization_lineage_seed)))
      (binding_destination(lineage_root e))(binding_asset(lineage_root e))=Some ACTIVE"
    using realization_exchange_inputs(7)
    by (simp add: reverse_exchange_effects_def realization_exchange_effects_def realization_effect_def)
  show ?thesis using realized.source_realization_finite_word_projection[OF references published active,
    where certificates=realization_certificates]
    by (simp add: reverse_exchange_source_def)
qed

lemma reverse_exchange_parent_success:
  "realization_succeeds realization_certificates reverse_exchange_effects
    (core_parent(coupled_core realization_lineage_seed))"
proof -
  have initial: "\<forall>root\<in>set[sample_binding 23,sample_binding 17]. \<forall>holder\<in>set[3,4].
    realization_units(core_parent(coupled_core realization_lineage_seed))root holder=
    realization_units(core_parent(coupled_core realization_lineage_seed))root holder" by simp
  note construction=realization_plan_from_is_constructive
    [OF realization_seed_financial reverse_exchange_inputs(1,2,3) initial reverse_exchange_inputs(4),
      where certificates=realization_certificates]
  show ?thesis using construction reverse_exchange_is_also_a_constructed_plan
    by (simp add: realization_plan_def)
qed

theorem the_two_orders_have_the_same_selected_funding:
  "\<forall>root\<in>set[sample_binding 17,sample_binding 23]. \<forall>holder\<in>set[3,4].
    realization_units(core_parent(coupled_core realization_exchange_finished))root holder=
      realization_units(core_parent(coupled_core reverse_exchange_source))root holder"
  using actual_two_root_plan_activates_every_source_dispatch
    reverse_exchange_activates_every_actual_source_consumer by auto

theorem the_two_successful_orders_have_different_actual_raw_replies:
  assumes forward_view: "core_parent(observed_core forward)=core_parent(coupled_core realization_exchange_finished)"
    and reverse_view: "core_parent(observed_core reverse)=core_parent(coupled_core reverse_exchange_source)"
  shows "snd(realized.execute_observed Read_Raw_Journal forward)\<noteq>
    snd(realized.execute_observed Read_Raw_Journal reverse)"
proof -
  have canonical: "\<forall>e\<in>set realization_exchange_effects. canonical_realization_effect e"
    and reverse_canonical: "\<forall>e\<in>set reverse_exchange_effects. canonical_realization_effect e"
    by (simp_all add: realization_exchange_effects_def reverse_exchange_effects_def
        canonical_realization_effect_def realization_effect_def)
  have distinct: "realization_exchange_effects\<noteq>reverse_exchange_effects"
    by (simp add: realization_exchange_effects_def reverse_exchange_effects_def
        realization_effect_def sample_binding_def example_binding_def)
  have journals: "machine_journal(core_parent(coupled_core realization_exchange_finished))\<noteq>
      machine_journal(core_parent(coupled_core reverse_exchange_source))"
    using successful_canonical_journals_reflect_the_whole_word
      [OF realization_exchange_parent_success reverse_exchange_parent_success canonical reverse_canonical] distinct
    by (simp only: realization_exchange_parent_projection reverse_exchange_parent_projection HOL.simp_thms)
  show ?thesis using journals by (simp add: forward_view reverse_view)
qed

theorem generated_observation_views_distinguish_the_two_orders:
  "snd(realized.execute_observed Read_Raw_Journal
      (initial_observed_finality(coupled_core realization_exchange_finished)))\<noteq>
    snd(realized.execute_observed Read_Raw_Journal
      (initial_observed_finality(coupled_core reverse_exchange_source)))"
  by (rule the_two_successful_orders_have_different_actual_raw_replies)
    (simp_all add: initial_observed_finality_def)

text \<open>The original source execution supplies both financial states.
  Both orders install the actual current authorization at every step and
  all descendant consumers succeed. Their selected funding tables agree;
  the existing raw-journal callback distinguishes their histories.
  The last theorem merely attaches an observation view to each generated
  core, and does not reset a durable call machine or prove crash recovery.
  Ordered words may be composed by concatenation. These observations forbid
  treating a permutation of successful effects as an equivalent whole API
  execution merely because it reaches the same allocation table.\<close>

end
