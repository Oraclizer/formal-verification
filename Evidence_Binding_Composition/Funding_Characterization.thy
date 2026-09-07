(* SPDX-License-Identifier: BSD-3-Clause *)
theory Funding_Characterization
  imports Funding_Realization
begin

section \<open>Arithmetic Admissibility and Actual Execution Images\<close>

definition funding_table_admissible :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow>
  reservation_machine \<Rightarrow> (transfer_binding \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "funding_table_admissible roots holders m target \<longleftrightarrow>
    (\<forall>root\<in>set roots. sum_list (map (target root) holders)=
      sum_list (map (realization_units m root) holders)) \<and>
    (\<forall>account. realization_account_total roots holders target account=
      realization_account_total roots holders (realization_units m) account)"

definition funding_effect_supported :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow>
  descendant_effect \<Rightarrow> bool" where
  "funding_effect_supported roots holders e \<longleftrightarrow>
    lineage_root e\<in>set roots \<and> lineage_from e\<in>set holders \<and>
    lineage_to e\<in>set holders \<and> 0<lineage_amount e \<and> canonical_realization_effect e"

definition funding_execution_image :: "transfer_binding list \<Rightarrow> nat list \<Rightarrow>
  (transfer_binding \<Rightarrow> source_certificate) \<Rightarrow> reservation_machine \<Rightarrow>
  (transfer_binding \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> descendant_effect list \<Rightarrow> bool" where
  "funding_execution_image roots holders certificates m target effects \<longleftrightarrow>
    (\<forall>e\<in>set effects. funding_effect_supported roots holders e) \<and>
    realization_succeeds certificates effects m \<and>
    (\<forall>root\<in>set roots. \<forall>h\<in>set holders.
      realization_units (run_realization certificates effects m) root h=target root h) \<and>
    destination_units (machine_state (run_realization certificates effects m))=
      destination_units (machine_state m) \<and>
    erase_lineage_state (run_realization certificates effects m)=erase_lineage_state m"

lemma characterization_integer_row_sum:
  "int (sum_list (map values entries))=sum_list (map (\<lambda>x. int (values x)) entries)"
  by (induction entries) simp_all

lemma characterization_sum_differences:
  fixes first second :: "'a \<Rightarrow> int"
  shows "sum_list (map (\<lambda>x. first x-second x) entries)=
    sum_list (map first entries)-sum_list (map second entries)"
  by (induction entries) (simp_all add: algebra_simps)

lemma characterization_sum_changes:
  fixes before after delta :: "'a \<Rightarrow> int"
  assumes changes: "\<forall>x\<in>set entries. after x=before x+delta x"
  shows "sum_list (map after entries)=sum_list (map before entries)+sum_list (map delta entries)"
  using changes by (induction entries) (auto simp: algebra_simps)

lemma selected_holder_descendant_delta_is_zero:
  assumes unique: "distinct holders"
    and same_root: "lineage_root effect=root"
    and sender: "lineage_from effect\<in>set holders"
    and recipient: "lineage_to effect\<in>set holders"
  shows "sum_list (map (\<lambda>h. descendant_delta (holder_account root h) effect) holders)=0"
proof -
  let ?amount = "int (lineage_amount effect)"
  let ?to = "holder_account root (lineage_to effect)"
  let ?from = "holder_account root (lineage_from effect)"
  have recipient_account: "?to\<in>holder_account root ` set holders"
    by (rule imageI[OF recipient])
  have sender_account: "?from\<in>holder_account root ` set holders"
    by (rule imageI[OF sender])
  have received: "sum_list (map (\<lambda>h. if holder_account root h=?to then ?amount else 0) holders)=?amount"
    using realization_holder_single_sum[OF unique, where root=root and account="?to" and weight="?amount"]
    by (simp only: recipient_account if_True)
  have spent: "sum_list (map (\<lambda>h. if holder_account root h=?from then ?amount else 0) holders)=?amount"
    using realization_holder_single_sum[OF unique, where root=root and account="?from" and weight="?amount"]
    by (simp only: sender_account if_True)
  have expansion: "map (\<lambda>h. descendant_delta (holder_account root h) effect) holders=
    map (\<lambda>h. (if holder_account root h=?to then ?amount else 0)-
      (if holder_account root h=?from then ?amount else 0)) holders"
    by (rule map_cong[OF refl]) (simp only: descendant_delta_def same_root eq_commute)
  show ?thesis by (simp only: expansion characterization_sum_differences received spent diff_self)
qed

section \<open>Every Successful Supported Word Preserves Each Row Total\<close>

lemma actual_supported_effect_preserves_row_total:
  assumes financial: "financial_history_agreement balances m"
    and success: "snd (realization_result certificates e m)=Descendant_Executed"
    and keys: "distinct (map binding_key roots)"
    and unique: "distinct holders"
    and supported: "funding_effect_supported roots holders e"
    and root_member: "root\<in>set roots"
  shows "sum_list (map (realization_units (fst (realization_result certificates e m)) root) holders)=
    sum_list (map (realization_units m root) holders)"
proof (cases "binding_key (lineage_root e)=binding_key root")
  case False
  have entries: "map (realization_units (fst (realization_result certificates e m)) root) holders=
      map (realization_units m root) holders"
  proof (rule map_cong[OF refl])
    fix h assume "h\<in>set holders"
    have separate: "binding_key root\<noteq>binding_key (lineage_root e)"
    proof (rule notI)
      assume equal: "binding_key root=binding_key (lineage_root e)"
      have same: "binding_key (lineage_root e)=binding_key root" by (rule sym[OF equal])
      show False by (rule notE[OF False same])
    qed
    show "realization_units (fst (realization_result certificates e m)) root h=realization_units m root h"
      unfolding realization_units_def
      by (rule realization_result_funding_frame, rule disjI1[OF separate])
  qed
  show ?thesis by (simp only: entries)
next
  case True
  let ?next = "fst (realization_result certificates e m)"
  let ?effect = "realization_effect (lineage_root e) (lineage_from e) (lineage_to e) (lineage_amount e)"
  have injective: "inj_on binding_key (set roots)"
    using keys by (simp only: distinct_map; blast)
  have effect_root: "lineage_root e\<in>set roots"
    and sender: "lineage_from e\<in>set holders"
    and recipient: "lineage_to e\<in>set holders"
    using supported unfolding funding_effect_supported_def by blast+
  have same_root: "lineage_root e=root"
    by (rule inj_onD[OF injective True effect_root root_member])
  have delta_zero: "sum_list (map (\<lambda>h. descendant_delta (holder_account root h) ?effect) holders)=0"
    by (rule selected_holder_descendant_delta_is_zero[OF unique])
      (simp_all add: realization_effect_def same_root sender recipient)
  have changes: "\<forall>h\<in>set holders. int (realization_units ?next root h)=
      int (realization_units m root h)+descendant_delta (holder_account root h) ?effect"
  proof (intro ballI)
    fix h assume "h\<in>set holders"
    show "int (realization_units ?next root h)=
      int (realization_units m root h)+descendant_delta (holder_account root h) ?effect"
      using realization_result_integer_changes(2)[OF financial success,
        where key="binding_key root" and account="holder_account root h"]
      by (simp only: realization_units_def True if_True HOL.simp_thms)
  qed
  have summed: "sum_list (map (\<lambda>h. int (realization_units ?next root h)) holders)=
    sum_list (map (\<lambda>h. int (realization_units m root h)) holders)+
      sum_list (map (\<lambda>h. descendant_delta (holder_account root h) ?effect) holders)"
    by (rule characterization_sum_changes[OF changes])
  have integer_equal: "int (sum_list (map (realization_units ?next root) holders))=
      int (sum_list (map (realization_units m root) holders))"
    using summed by (simp only: characterization_integer_row_sum delta_zero add_0)
  show ?thesis using integer_equal by simp
qed

theorem actual_supported_word_preserves_row_total:
  assumes financial: "financial_history_agreement balances m"
    and success: "realization_succeeds certificates effects m"
    and keys: "distinct (map binding_key roots)"
    and unique: "distinct holders"
    and supported: "\<forall>e\<in>set effects. funding_effect_supported roots holders e"
    and root_member: "root\<in>set roots"
  shows "sum_list (map (realization_units (run_realization certificates effects m) root) holders)=
    sum_list (map (realization_units m root) holders)"
  using financial success supported
proof (induction effects arbitrary:m)
  case Nil
  then show ?case by simp
next
  case (Cons e effects)
  let ?next = "fst (realization_result certificates e m)"
  have reply: "snd (realization_result certificates e m)=Descendant_Executed"
    using Cons.prems(2) by simp
  have effect_support: "funding_effect_supported roots holders e"
    using Cons.prems(3) by simp
  have head: "sum_list (map (realization_units ?next root) holders)=
      sum_list (map (realization_units m root) holders)"
    by (rule actual_supported_effect_preserves_row_total
      [OF Cons.prems(1) reply keys unique effect_support root_member])
  have next_financial: "financial_history_agreement balances ?next"
    by (rule realization_result_financial[OF Cons.prems(1) reply])
  have tail_success: "realization_succeeds certificates effects ?next"
    using Cons.prems(2) by simp
  have tail_support: "\<forall>d\<in>set effects. funding_effect_supported roots holders d"
    using Cons.prems(3) by simp
  have tail: "sum_list (map (realization_units (run_realization certificates effects ?next) root) holders)=
      sum_list (map (realization_units ?next root) holders)"
    by (rule Cons.IH[OF next_financial tail_success tail_support])
  show ?case by (simp only: run_realization.simps tail head)
qed

lemma supported_word_preserves_outside_funding:
  assumes supported: "\<forall>e\<in>set effects. funding_effect_supported roots holders e"
    and outside: "(key,account)\<notin>realization_cells roots holders"
  shows "funded_units (machine_state (run_realization certificates effects m)) (key,account)=
    funded_units (machine_state m) (key,account)"
proof (rule run_realization_funding_frame, intro ballI)
  fix e assume member: "e\<in>set effects"
  have support: "funding_effect_supported roots holders e"
    by (rule bspec[OF supported member])
  have root_member: "lineage_root e\<in>set roots"
    and from_member: "lineage_from e\<in>set holders"
    and to_member: "lineage_to e\<in>set holders"
    using support unfolding funding_effect_supported_def by blast+
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

lemma characterization_account_total_cong:
  assumes agree: "\<forall>root\<in>set roots. \<forall>h\<in>set holders. first root h=second root h"
  shows "realization_account_total roots holders first account=
    realization_account_total roots holders second account"
  unfolding realization_account_total_def
proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
  fix root assume member: "root\<in>set roots"
  show "sum_list (map (\<lambda>h. if holder_account root h=account then int (first root h) else 0) holders)=
    sum_list (map (\<lambda>h. if holder_account root h=account then int (second root h) else 0) holders)"
  proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
    fix h assume holder: "h\<in>set holders"
    have at_root: "\<forall>h\<in>set holders. first root h=second root h"
      by (rule bspec[OF agree member])
    have at_holder: "first root h=second root h" by (rule bspec[OF at_root holder])
    show "(if holder_account root h=account then int (first root h) else 0)=
      (if holder_account root h=account then int (second root h) else 0)"
      by (simp only: at_holder)
  qed
qed

lemma supported_word_preserves_outside_total:
  assumes keys: "distinct (map binding_key roots)"
    and supported: "\<forall>e\<in>set effects. funding_effect_supported roots holders e"
  shows "realization_outside_total roots holders (run_realization certificates effects m) account=
    realization_outside_total roots holders m account"
  unfolding realization_outside_total_def
proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
  fix root assume member: "root\<in>set roots"
  show "(if account\<in>holder_account root ` set holders then 0
      else int (funded_units (machine_state (run_realization certificates effects m)) (binding_key root,account)))=
    (if account\<in>holder_account root ` set holders then 0
      else int (funded_units (machine_state m) (binding_key root,account)))"
  proof (cases "account\<in>holder_account root ` set holders")
    case True
    show ?thesis by (simp only: True if_True)
  next
    case False
    have outside: "(binding_key root,account)\<notin>realization_cells roots holders"
    proof (rule notI)
      assume selected: "(binding_key root,account)\<in>realization_cells roots holders"
      have selected_iff: "(binding_key root,account)\<in>realization_cells roots holders \<longleftrightarrow>
          account\<in>holder_account root ` set holders"
        by (rule realization_selected_row[OF keys member])
      have hit: "account\<in>holder_account root ` set holders"
        by (rule iffD1[OF selected_iff selected])
      show False by (rule notE[OF False hit])
    qed
    have frame: "funded_units (machine_state (run_realization certificates effects m)) (binding_key root,account)=
        funded_units (machine_state m) (binding_key root,account)"
      by (rule supported_word_preserves_outside_funding[OF supported outside])
    show ?thesis by (simp only: False if_False frame)
  qed
qed

section \<open>Final Pooled Equality Forces the Account Margins\<close>

theorem actual_successful_image_forces_admissibility:
  assumes financial: "financial_history_agreement balances m"
    and keys: "distinct (map binding_key roots)"
    and unique: "distinct holders"
    and image: "funding_execution_image roots holders certificates m target effects"
  shows "funding_table_admissible roots holders m target"
proof -
  let ?after = "run_realization certificates effects m"
  have supported: "\<forall>e\<in>set effects. funding_effect_supported roots holders e"
    and success: "realization_succeeds certificates effects m"
    and realized: "\<forall>root\<in>set roots. \<forall>h\<in>set holders. realization_units ?after root h=target root h"
    and pooled: "destination_units (machine_state ?after)=destination_units (machine_state m)"
    using image unfolding funding_execution_image_def by blast+
  have rows: "\<forall>root\<in>set roots. sum_list (map (target root) holders)=
      sum_list (map (realization_units m root) holders)"
  proof (intro ballI)
    fix root assume member: "root\<in>set roots"
    have conserved: "sum_list (map (realization_units ?after root) holders)=
        sum_list (map (realization_units m root) holders)"
      by (rule actual_supported_word_preserves_row_total[OF financial success keys unique supported member])
    have targets: "map (realization_units ?after root) holders=map (target root) holders"
    proof (rule map_cong[OF refl])
      fix h assume holder: "h\<in>set holders"
      have row: "\<forall>h\<in>set holders. realization_units ?after root h=target root h"
        by (rule bspec[OF realized member])
      show "realization_units ?after root h=target root h" by (rule bspec[OF row holder])
    qed
    show "sum_list (map (target root) holders)=sum_list (map (realization_units m root) holders)"
      using conserved by (simp only: targets)
  qed
  have effect_roots: "\<forall>e\<in>set effects. lineage_root e\<in>set roots"
  proof (intro ballI)
    fix e assume member: "e\<in>set effects"
    have "funding_effect_supported roots holders e" by (rule bspec[OF supported member])
    then show "lineage_root e\<in>set roots" unfolding funding_effect_supported_def by (rule conjunct1)
  qed
  have columns: "\<forall>account. realization_account_total roots holders target account=
      realization_account_total roots holders (realization_units m) account"
  proof (intro allI)
    fix account
    have residual: "realization_residual roots ?after account=realization_residual roots m account"
      by (rule run_realization_residual[OF financial success keys effect_roots])
    have total_roots: "sum_list (map (\<lambda>root. int (funded_units (machine_state ?after) (binding_key root,account))) roots)=
        sum_list (map (\<lambda>root. int (funded_units (machine_state m) (binding_key root,account))) roots)"
      using residual unfolding realization_residual_def by (simp only: pooled; linarith)
    have outside: "realization_outside_total roots holders ?after account=realization_outside_total roots holders m account"
      by (rule supported_word_preserves_outside_total[OF keys supported])
    have after_split: "sum_list (map (\<lambda>root. int (funded_units (machine_state ?after) (binding_key root,account))) roots)=
        realization_account_total roots holders (realization_units ?after) account+
          realization_outside_total roots holders ?after account"
      by (rule realization_total_decomposition[OF unique])
    have before_split: "sum_list (map (\<lambda>root. int (funded_units (machine_state m) (binding_key root,account))) roots)=
        realization_account_total roots holders (realization_units m) account+
          realization_outside_total roots holders m account"
      by (rule realization_total_decomposition[OF unique])
    have current_total: "realization_account_total roots holders (realization_units ?after) account=
        realization_account_total roots holders (realization_units m) account"
      using total_roots outside after_split before_split by linarith
    have target_total: "realization_account_total roots holders (realization_units ?after) account=
        realization_account_total roots holders target account"
      by (rule characterization_account_total_cong[OF realized])
    show "realization_account_total roots holders target account=
        realization_account_total roots holders (realization_units m) account"
      using current_total by (simp only: target_total)
  qed
  show ?thesis unfolding funding_table_admissible_def by (rule conjI[OF rows columns])
qed

context source_attestation
begin

theorem admissible_funding_has_the_constructed_actual_image:
  fixes certificates :: "transfer_binding \<Rightarrow> source_certificate"
  assumes contract: "reservation_contract balances m"
    and credited: "\<forall>root\<in>set roots. root\<in>set (credit_history (received_messages (machine_state m)))"
    and keys: "distinct (map binding_key roots)"
    and unique: "distinct holders"
    and admissible: "funding_table_admissible roots holders m target"
  shows "funding_execution_image roots holders certificates m target (realization_plan roots holders m target)"
proof -
  have rows: "\<forall>root\<in>set roots. sum_list (map (target root) holders)=
      sum_list (map (realization_units m root) holders)"
    and columns: "\<forall>account. realization_account_total roots holders target account=
      realization_account_total roots holders (realization_units m) account"
    using admissible unfolding funding_table_admissible_def by blast+
  note construction = finite_funding_realization[OF contract credited keys unique rows columns,
    where certificates=certificates]
  show ?thesis
    using construction
    unfolding funding_execution_image_def funding_effect_supported_def
    by (simp only: realization_run_is_parent_execution[symmetric]; blast)
qed

theorem finite_funding_admissibility_iff_realization:
  fixes certificates :: "transfer_binding \<Rightarrow> source_certificate"
  assumes contract: "reservation_contract balances m"
    and credited: "\<forall>root\<in>set roots. root\<in>set (credit_history (received_messages (machine_state m)))"
    and keys: "distinct (map binding_key roots)"
    and unique: "distinct holders"
  shows "funding_table_admissible roots holders m target \<longleftrightarrow>
    (\<exists>effects. funding_execution_image roots holders certificates m target effects)"
proof
  assume admissible: "funding_table_admissible roots holders m target"
  have actual: "funding_execution_image roots holders certificates m target (realization_plan roots holders m target)"
    by (rule admissible_funding_has_the_constructed_actual_image[OF contract credited keys unique admissible])
  show "\<exists>effects. funding_execution_image roots holders certificates m target effects"
    by (rule exI[of _ "realization_plan roots holders m target"], rule actual)
next
  assume "\<exists>effects. funding_execution_image roots holders certificates m target effects"
  then obtain effects where actual: "funding_execution_image roots holders certificates m target effects" by blast
  have financial: "financial_history_agreement balances m"
    using contract unfolding reservation_contract_def by blast
  show "funding_table_admissible roots holders m target"
    by (rule actual_successful_image_forces_admissibility[OF financial keys unique actual])
qed

theorem characterized_image_has_actual_parent_execution_and_source_frame:
  assumes contract: "reservation_contract balances m"
    and image: "funding_execution_image roots holders certificates m target effects"
  shows "run_realization certificates effects m=
      run_reservations balances (realization_actions certificates effects) m \<and>
    machine_journal (run_realization certificates effects m)=machine_journal m@map Descendant_Event effects \<and>
    source_units (machine_state (run_realization certificates effects m))=source_units (machine_state m) \<and>
    source_effects (machine_state (run_realization certificates effects m))=source_effects (machine_state m) \<and>
    received_messages (machine_state (run_realization certificates effects m))=received_messages (machine_state m) \<and>
    reservation_contract balances (run_realization certificates effects m)"
proof -
  have success: "realization_succeeds certificates effects m"
    and canonical: "\<forall>e\<in>set effects. canonical_realization_effect e"
    using image unfolding funding_execution_image_def funding_effect_supported_def by blast+
  have journal: "machine_journal (run_realization certificates effects m)=machine_journal m@map Descendant_Event effects"
    by (rule conjunct1[OF run_realization_exact_history[OF success canonical]])
  have static: "realization_static_state (run_realization certificates effects m)=realization_static_state m"
    by (rule run_realization_static)
  note frame = realization_static_supplies_source_frame[OF static]
  have after_contract: "reservation_contract balances (run_realization certificates effects m)"
    using finite_execution_preserves_reservation_contract[OF contract,
      where actions="realization_actions certificates effects"]
    by (simp only: realization_run_is_parent_execution[symmetric])
  show ?thesis using journal frame after_contract
    by (simp only: realization_run_is_parent_execution[symmetric] HOL.simp_thms; blast)
qed

end

section \<open>Empty Selections and the Exact Scope of the Characterization\<close>

lemma empty_roots_are_admissible [simp]:
  "funding_table_admissible [] holders m target"
  by (simp add: funding_table_admissible_def realization_account_total_def)

lemma empty_holders_are_admissible [simp]:
  "funding_table_admissible roots [] m target"
  by (simp add: funding_table_admissible_def realization_account_total_def)

lemma empty_roots_have_the_empty_actual_image [simp]:
  "funding_execution_image [] holders certificates m target []"
  by (simp add: funding_execution_image_def)

lemma empty_holders_have_the_empty_actual_image [simp]:
  "funding_execution_image roots [] certificates m target []"
  by (simp add: funding_execution_image_def)

text \<open>Admissibility contains only the initial and target arithmetic margins.
  Successful execution and the supported positive effect word occur on the image
  side of the equivalence. The forward implication uses the existing constructive
  drain and distribute word. The reverse implication follows from actual
  per-root funding changes and the actual pooled residual, including funding
  outside the selected cells.

  The selected holders use each root's immutable destination and asset through
  holder_account. Equal holder numbers on different destination accounts are not
  one column. The equivalence supplies the existing current authorization probes;
  it is not a reachability theorem under every fixed restrictive policy. Final
  erased-state equality does not erase intermediate observations or the added
  journal. The characterized language is this finite allocation language of
  actual parent operations, not all normal forms, physical adapters or compiled
  runtime APIs.\<close>

end
