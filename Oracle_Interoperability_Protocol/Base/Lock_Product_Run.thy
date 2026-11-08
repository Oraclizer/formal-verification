theory Lock_Product_Run
  imports Lock_Endpoints
begin

section \<open>Interleaved product lock and finality actions\<close>

datatype lock_product_action =
    Lock_Submit lock_entry product_principal client_call_id product_envelope "product_lock_credential option"
  | Lock_Install product_principal nat "(nat \<times> lock_context) list" "product_session_id \<Rightarrow> product_session_binding option"
  | Lock_Driver_Connection authority_connection

definition initial_lock_world where
  "initial_lock_world balances regulatory contexts durable = \<lparr>product_durable = durable,
    product_calls = initial_call_machine (initial_finality_core balances regulatory contexts)\<rparr>"

fun product_command_endpoint where
  "product_command_endpoint (Client_Terminal cert) = None"
| "product_command_endpoint (Client_Protocol endpoint index intent) = Some endpoint"
| "product_command_endpoint (Client_Regulatory endpoint index r) = Some endpoint"
| "product_command_endpoint (Client_Publication key) = None"

definition registered_lock_envelope where
  "registered_lock_envelope registered envelope \<longleftrightarrow>
    (case product_command_endpoint (envelope_command envelope) of None \<Rightarrow> True
     | Some endpoint \<Rightarrow> endpoint \<in> registered)"

definition lock_context_batch_is_newer where
  "lock_context_batch_is_newer registered epoch changes s \<longleftrightarrow>
    changes \<noteq> [] \<and> distinct (map fst changes) \<and> set (map fst changes) = registered \<and>
    (\<forall>(endpoint, cfg) \<in> set changes. context_endpoint (lock_authority cfg) = endpoint \<and>
      context_authority_epoch (lock_authority cfg) = epoch) \<and>
    cut_authority_epoch (current_product_cut s) < epoch"

text \<open>The registered endpoints share one product authority epoch. Their
  context installation is a single product action. A partially updated batch
  cannot advance the epoch. Driver connection events represent internal adapter
  signals and cannot be submitted as client commands.\<close>

context source_attestation
begin

fun lock_product_step where
  "lock_product_step permitted verified maintainers registered (Lock_Submit entry who call_id envelope supplied) s =
    (if registered_lock_envelope registered envelope
     then submit_lock_entry permitted verified entry who call_id envelope supplied s else s)"
| "lock_product_step permitted verified maintainers registered (Lock_Install who epoch changes sessions) s =
    (if who \<in> maintainers \<and> lock_context_batch_is_newer registered epoch changes s then
      (product_apply_public (map Apply_Authority_Input changes) s)\<lparr>product_durable :=
        (product_durable s)\<lparr>product_authority_epoch := epoch,
          product_sessions := sessions\<rparr>\<rparr>
     else s)"
| "lock_product_step permitted verified maintainers registered (Lock_Driver_Connection connection) s =
    product_apply_public [Set_Authority_Connection connection] s"

fun run_lock_product where
  "run_lock_product permitted verified maintainers registered [] s = s"
| "run_lock_product permitted verified maintainers registered (action # rest) s =
    run_lock_product permitted verified maintainers registered rest
      (lock_product_step permitted verified maintainers registered action s)"

lemma authorized_context_install_sets_current_epoch:
  assumes "who \<in> maintainers" "lock_context_batch_is_newer registered epoch changes s"
  shows "cut_authority_epoch (current_product_cut
     (lock_product_step permitted verified maintainers registered (Lock_Install who epoch changes sessions) s)) = epoch"
  using assms by (simp add: product_apply_public_def current_product_cut_def)

lemma context_install_invalidates_old_credential:
  assumes "who \<in> maintainers" "lock_context_batch_is_newer registered epoch changes s"
    and "credential_epoch old = cut_authority_epoch (current_product_cut s)"
  shows "let next = lock_product_step permitted verified maintainers registered (Lock_Install who epoch changes sessions) s
    in submit_lock_entry permitted verified entry actor call_id envelope (Some old) next = next"
proof -
  have less: "credential_epoch old < epoch"
    using assms(2,3) by (simp add: lock_context_batch_is_newer_def)
  show ?thesis unfolding Let_def
    by (rule every_lock_entry_rejects_older_authority_epoch)
      (simp only: authorized_context_install_sets_current_epoch[OF assms(1,2)] less)
qed

lemma driver_failure_preserves_authoritative_state:
  "call_authority_state (product_calls (lock_product_step permitted verified maintainers registered
     (Lock_Driver_Connection Authority_Disconnected) s)) = call_authority_state (product_calls s)"
  by (simp add: product_apply_public_def)

lemma lock_product_step_is_public_segment:
  "\<exists>word. product_calls (lock_product_step permitted verified maintainers registered action s) =
     finality_calls.run_calls word (product_calls s)"
proof (cases action)
  case (Lock_Submit entry who call_id envelope supplied)
  show ?thesis
  proof (cases "registered_lock_envelope registered envelope")
    case True
    with Lock_Submit show ?thesis by (simp add: lock_submit_is_public_segment)
  next
    case False
    with Lock_Submit show ?thesis by (intro exI[of _ "[]"]) simp
  qed
next
  case (Lock_Install who epoch changes sessions)
  show ?thesis
  proof (cases "who \<in> maintainers \<and> lock_context_batch_is_newer registered epoch changes s")
    case True
    with Lock_Install show ?thesis
      by (intro exI[of _ "map Apply_Authority_Input changes"])
        (simp add: product_apply_public_def)
  next
    case False
    show ?thesis
      by (intro exI[of _ "[]"])
        (simp only: Lock_Install lock_product_step.simps False if_False finality_calls.run_calls.simps)
  qed
next
  case (Lock_Driver_Connection connection)
  then show ?thesis by (intro exI[of _ "[Set_Authority_Connection connection]"])
    (simp add: product_apply_public_def)
qed

lemma lock_public_segments_append:
  "finality_calls.run_calls (first @ second) m =
    finality_calls.run_calls second (finality_calls.run_calls first m)"
  by (induction first arbitrary: m) simp_all

lemma lock_product_trace_is_public_word:
  "\<exists>word. product_calls (run_lock_product permitted verified maintainers registered actions s) =
     finality_calls.run_calls word (product_calls s)"
proof (induction actions arbitrary: s)
  case Nil
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons action actions)
  let ?next = "lock_product_step permitted verified maintainers registered action s"
  obtain first where first: "product_calls ?next = finality_calls.run_calls first (product_calls s)"
    using lock_product_step_is_public_segment by blast
  obtain rest where rest: "product_calls (run_lock_product permitted verified maintainers registered actions ?next) =
    finality_calls.run_calls rest (product_calls ?next)" using Cons.IH by blast
  show ?case by (intro exI[of _ "first @ rest"]) (simp add: rest first lock_public_segments_append)
qed

end

end
