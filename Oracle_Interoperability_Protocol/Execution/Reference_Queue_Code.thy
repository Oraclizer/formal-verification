theory Reference_Queue_Code
  imports "OIP_Reference_Profile.Reference_Queue_Consumption"
begin

definition native_queue_has_one_target where
  "native_queue_has_one_target state \<longleftrightarrow>
     (\<forall>key job. settlement_jobs state key = Some job \<longrightarrow> secondary_target job = settlement_target state)"

definition native_secondary_ack_step where
  "native_secondary_ack_step verify ack state =
    (let key = ack_settlement_key ack in
      case settlement_jobs state key of None \<Rightarrow> (state, False)
      | Some job \<Rightarrow>
        if key = settlement_key (secondary_publication job) \<and>
           ack_publication ack = secondary_publication job \<and>
           ack_target ack = secondary_target job \<and>
           ack_target ack = settlement_target state \<and>
           secondary_attempts job > 0 \<and> verify ack
        then (update_secondary_job key (job\<lparr>secondary_state := Secondary_Completed\<rparr>) state, True)
        else (state, False))"

theorem native_exact_ack_matches_the_scheduled_product_state_and_reply:
  assumes target_bound: "native_queue_has_one_target state"
  shows "map_prod id Settlement_Changed (native_secondary_ack_step verify ack state) =
      execute_settlement_action verify (Exact_Acknowledge ack) state"
proof (cases "settlement_jobs state (ack_settlement_key ack)")
  case None
  then show ?thesis by (simp add: native_secondary_ack_step_def execute_settlement_action_def
    step_settlement_slot_def Let_def fun_upd_idem)
next
  case (Some job)
  have target: "secondary_target job = settlement_target state"
    using target_bound Some unfolding native_queue_has_one_target_def by blast
  show ?thesis using Some target
    by (simp add: native_secondary_ack_step_def execute_settlement_action_def
      step_settlement_slot_def exact_secondary_ack_def update_secondary_job_def Let_def fun_upd_idem)
qed

lemma the_native_ack_check_never_overwrites_the_primary_decision:
  "settlement_primary (fst (native_secondary_ack_step verify ack state)) = settlement_primary state"
  by (simp add: native_secondary_ack_step_def update_secondary_job_def Let_def split: option.splits if_splits)

lemma an_exact_job_target_alone_cannot_override_the_authority_target:
  assumes "settlement_jobs state (ack_settlement_key ack) = Some job"
    "ack_target ack = secondary_target job" "ack_target ack \<noteq> settlement_target state"
  shows "native_secondary_ack_step verify ack state = (state, False)"
  using assms by (simp add: native_secondary_ack_step_def Let_def)

record rust_secondary_row =
  rust_secondary_commitment :: product_publication
  rust_secondary_receiver :: nat
  rust_secondary_tries :: nat
  rust_secondary_phase :: secondary_status

record 'primary rust_queue_image =
  rust_queue_primary :: 'primary
  rust_queue_receiver :: nat
  rust_queue_rows :: "settlement_identity \<Rightarrow> rust_secondary_row option"

definition rust_secondary_of where
  "rust_secondary_of row = \<lparr>rust_secondary_commitment = secondary_publication row,
     rust_secondary_receiver = secondary_target row, rust_secondary_tries = secondary_attempts row,
     rust_secondary_phase = secondary_state row\<rparr>"

definition rust_queue_matches where
  "rust_queue_matches primary_related code model \<longleftrightarrow>
    primary_related (rust_queue_primary code) (settlement_primary model) \<and>
    rust_queue_receiver code = settlement_target model \<and>
    rust_queue_rows code = map_option rust_secondary_of \<circ> settlement_jobs model"

definition rust_acknowledge_row where
  "rust_acknowledge_row verify ack code =
    (let key = ack_settlement_key ack in
      case rust_queue_rows code key of None \<Rightarrow> (code, False)
      | Some row \<Rightarrow> if key = settlement_key (rust_secondary_commitment row) \<and>
          ack_publication ack = rust_secondary_commitment row \<and> ack_target ack = rust_secondary_receiver row \<and>
          ack_target ack = rust_queue_receiver code \<and> rust_secondary_tries row > 0 \<and> verify ack
        then (code\<lparr>rust_queue_rows := (rust_queue_rows code)(key := Some (row\<lparr>rust_secondary_phase := Secondary_Completed\<rparr>))\<rparr>, True)
        else (code, False))"

theorem rust_ack_consumes_the_related_queue_and_preserves_its_primary_and_reply:
  assumes initial: "rust_queue_matches related code model"
    and targets: "native_queue_has_one_target model"
  shows "let native = rust_acknowledge_row verify ack code;
       spec = execute_settlement_action verify (Exact_Acknowledge ack) model
    in rust_queue_matches related (fst native) (fst spec) \<and>
       rust_queue_primary (fst native) = rust_queue_primary code \<and> Settlement_Changed (snd native) = snd spec"
proof -
  let ?native = "rust_acknowledge_row verify ack code"
  let ?step = "native_secondary_ack_step verify ack model"
  have lookup: "rust_queue_rows code key = map_option rust_secondary_of (settlement_jobs model key)" for key
    using initial by (simp add: rust_queue_matches_def)
  have simulation: "rust_queue_matches related (fst ?native) (fst ?step) \<and>
      rust_queue_primary (fst ?native) = rust_queue_primary code \<and> snd ?native = snd ?step"
    using initial lookup[of "ack_settlement_key ack"] by (cases "settlement_jobs model (ack_settlement_key ack)")
      (auto simp: rust_queue_matches_def rust_acknowledge_row_def rust_secondary_of_def native_secondary_ack_step_def
        update_secondary_job_def Let_def fun_eq_iff)
  let ?spec = "execute_settlement_action verify (Exact_Acknowledge ack) model"
  have exact: "map_prod id Settlement_Changed ?step = ?spec"
    by (rule native_exact_ack_matches_the_scheduled_product_state_and_reply[OF targets])
  have state: "fst ?spec = fst ?step" and reply: "snd ?spec = Settlement_Changed (snd ?step)"
    using exact[symmetric] by (simp_all)
  show ?thesis using simulation state reply by (simp add: Let_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms native_exact_ack_matches_the_scheduled_product_state_and_reply
      rust_ack_consumes_the_related_queue_and_preserves_its_primary_and_reply
      the_native_ack_check_never_overwrites_the_primary_decision
      an_exact_job_target_alone_cannot_override_the_authority_target})
  then () else error "Unexpected oracle in the native ACK relation"
\<close>

end
