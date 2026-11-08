theory Freeze_Interval
  imports Frozen_Spend
begin

definition no_thaw_for_asset where
  "no_thaw_for_asset asset word \<longleftrightarrow>
    (\<forall>(source, action, target) \<in> set word. target = asset \<longrightarrow> action \<notin> {UNFREEZE, RELEASE})"

lemma protected_mode_survives_a_non_thaw_transition:
  assumes "protected_freeze_mode mode" "action \<notin> {UNFREEZE, RELEASE}" "reg_transition mode action = Some next"
  shows "protected_freeze_mode next"
  using assms by (cases mode; cases action) (simp_all add: protected_freeze_mode_def)

lemma regulatory_sync_keeps_other_asset_mode:
  assumes "sync source action target state = Some next" "asset \<noteq> target"
  shows "get_reg_state next observer asset = get_reg_state state observer asset"
proof -
  from assms(1) obtain locked updated where lock: "acquire_lock state target = Some locked"
    and updated_state: "next = release_lock (update_all_chains locked target updated (connected_chains state target)) target"
    by (auto simp: sync_def Let_def split: option.splits)
  show ?thesis using assms(2)
    by (simp add: updated_state get_reg_state_def get_asset_state_def release_lock_chains update_all_chains_other_asset acquire_lock_chains[OF lock])
qed

lemma regulatory_sync_keeps_protection_until_thaw:
  assumes valid: "valid_state state"
    and actual: "get_reg_state state observer asset = Some mode" and protected: "protected_freeze_mode mode"
    and sync: "sync source action target state = Some next"
    and not_thaw: "target = asset \<Longrightarrow> action \<notin> {UNFREEZE, RELEASE}"
  shows "\<exists>next_mode. get_reg_state next observer asset = Some next_mode \<and> protected_freeze_mode next_mode"
proof (cases "target = asset")
  case False
  have same: "get_reg_state next observer asset = get_reg_state state observer asset"
    by (rule regulatory_sync_keeps_other_asset_mode[OF sync]) (use False in simp)
  show ?thesis by (intro exI[of _ mode]) (simp add: same actual protected)
next
  case True
  obtain src_mode next_mode where source: "get_reg_state state source asset = Some src_mode"
    and transition: "reg_transition src_mode action = Some next_mode"
    using sync True by (auto simp: sync_def Let_def split: option.splits)
  have equal: "src_mode = mode"
    using valid source actual unfolding valid_state_def consistent_state_def by blast
  have connected: "observer \<in> connected_chains state asset"
    using actual by (auto simp: connected_chains_def asset_exists_def get_reg_state_def split: option.splits)
  have result: "get_reg_state next observer asset = Some next_mode"
    by (rule regulatory_homomorphism[OF source transition sync[unfolded True] connected])
  have still: "protected_freeze_mode next_mode"
    by (rule protected_mode_survives_a_non_thaw_transition[OF protected not_thaw[OF True]])
      (use transition equal in simp)
  show ?thesis by (intro exI[of _ next_mode]) (simp add: result still)
qed

context source_attestation
begin

lemma actual_regulatory_word_is_empty_or_one_action:
  "emitted_regulatory_word action s = [] \<or> (\<exists>source operation asset. emitted_regulatory_word action s = [(source, operation, asset)])"
  by (cases action) (auto split: if_splits message_operation.splits)

lemma actual_finality_step_keeps_freeze_without_thaw:
  assumes valid: "valid_state (receiver_snapshot (core_regulatory s))"
    and current: "get_reg_state (receiver_snapshot (core_regulatory s)) observer asset = Some mode"
    and protected: "protected_freeze_mode mode"
    and no_thaw: "no_thaw_for_asset asset (emitted_regulatory_word action s)"
  shows "\<exists>next_mode. get_reg_state (receiver_snapshot (core_regulatory (finality_step action s))) observer asset = Some next_mode
    \<and> protected_freeze_mode next_mode"
proof -
  let ?before = "receiver_snapshot (core_regulatory s)"
  let ?after = "receiver_snapshot (core_regulatory (finality_step action s))"
  have lifted: "run_regulatory_word (emitted_regulatory_word action s) ?before = Some ?after"
    by (rule actual_finality_step_refines_regulatory_word)
  from actual_regulatory_word_is_empty_or_one_action[of action s] show ?thesis
  proof
    assume empty: "emitted_regulatory_word action s = []"
    have same: "?before = ?after" using lifted unfolding empty by simp
    show ?thesis using current protected unfolding same by (intro exI[of _ mode]) simp
  next
    assume "\<exists>source operation target. emitted_regulatory_word action s = [(source, operation, target)]"
    then obtain source operation target where word: "emitted_regulatory_word action s = [(source, operation, target)]" by blast
    have step: "sync source operation target ?before = Some ?after"
      using lifted unfolding word by (simp split: option.splits)
    have allowed: "target = asset \<Longrightarrow> operation \<notin> {UNFREEZE, RELEASE}"
      using no_thaw unfolding word no_thaw_for_asset_def by simp
    show ?thesis by (rule regulatory_sync_keeps_protection_until_thaw[OF valid current protected step allowed])
  qed
qed

fun continuation_has_no_thaw where
  "continuation_has_no_thaw asset [] s = True"
| "continuation_has_no_thaw asset (action # rest) s =
    (no_thaw_for_asset asset (emitted_regulatory_word action s) \<and>
       continuation_has_no_thaw asset rest (finality_step action s))"

theorem completed_freeze_survives_every_actual_continuation_without_thaw:
  assumes "valid_state (receiver_snapshot (core_regulatory s))"
    "get_reg_state (receiver_snapshot (core_regulatory s)) observer asset = Some mode"
    "protected_freeze_mode mode" "continuation_has_no_thaw asset actions s"
  shows "\<exists>next_mode. get_reg_state (receiver_snapshot (core_regulatory (run_finality actions s))) observer asset = Some next_mode
    \<and> protected_freeze_mode next_mode"
  using assms
proof (induction actions arbitrary: s mode)
  case Nil
  then show ?case by (intro exI[of _ mode]) simp
next
  case (Cons action actions)
  have local_guard: "no_thaw_for_asset asset (emitted_regulatory_word action s)"
    using Cons.prems(4) by simp
  obtain middle where mid: "get_reg_state (receiver_snapshot (core_regulatory (finality_step action s))) observer asset = Some middle"
    "protected_freeze_mode middle"
    using actual_finality_step_keeps_freeze_without_thaw[OF Cons.prems(1,2,3) local_guard] by blast
  have valid_next: "valid_state (receiver_snapshot (core_regulatory (finality_step action s)))"
    by (rule actual_finality_step_preserves_cdsp[OF Cons.prems(1)])
  have later: "continuation_has_no_thaw asset actions (finality_step action s)"
    using Cons.prems(4) by simp
  show ?case using Cons.IH[OF valid_next mid later] by simp
qed

theorem ordinary_spend_after_freeze_without_thaw_is_rejected:
  assumes valid: "valid_state (receiver_snapshot (core_regulatory s))"
    and frozen: "get_reg_state (receiver_snapshot (core_regulatory s))
      (binding_destination root) (binding_asset (request_binding r)) = Some FROZEN"
    and no_thaw: "continuation_has_no_thaw (binding_asset (request_binding r)) actions s"
    and op: "binding_operation (request_binding r) = Ordinary_Transfer_Effect"
  shows "let current = run_finality actions s;
       result = invoke_protocol endpoint (core_epoch current) index (Descendant_Intent r root sender recipient amount) current
    in snd result \<in> {Finality_Rejected, Protocol_Response Request_Rejected} \<and>
       machine_state (core_parent (fst result)) = machine_state (core_parent current) \<and>
       core_records (fst result) = core_records current \<and> core_regulatory (fst result) = core_regulatory current"
proof -
  let ?current = "run_finality actions s"
  have protected: "protected_freeze_mode FROZEN" by (simp add: protected_freeze_mode_def)
  obtain mode where state: "get_reg_state (receiver_snapshot (core_regulatory ?current))
      (binding_destination root) (binding_asset (request_binding r)) = Some mode"
    and mode: "protected_freeze_mode mode"
    using completed_freeze_survives_every_actual_continuation_without_thaw[OF valid frozen protected no_thaw] by blast
  have metadata: "get_reg_state (lock_metadata (current_lock_view ?current endpoint))
      (binding_destination root) (binding_asset (request_binding r)) = Some mode"
    using state by (simp add: current_lock_view_def)
  show ?thesis unfolding Let_def
    using protected_ordinary_spending_cannot_change_authoritative_balances[OF op metadata mode,
      where index=index and sender=sender and recipient=recipient and amount=amount, unfolded Let_def] .
qed

end

end
