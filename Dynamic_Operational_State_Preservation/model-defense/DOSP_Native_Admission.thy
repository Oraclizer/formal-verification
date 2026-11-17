theory DOSP_Native_Admission
  imports DOSP_Joint_Failure
begin

fun preparation_binding :: "client_command \<Rightarrow> transfer_binding option" where
  "preparation_binding (Client_Terminal certificate) = Some (statement_binding (certificate_statement certificate))"
| "preparation_binding (Client_Protocol endpoint index intent) =
    (case intent of Certificate_Intent certificate \<Rightarrow> Some (statement_binding (certificate_statement certificate))
      | _ \<Rightarrow> map_option request_binding (intent_request intent))"
| "preparation_binding _ = None"

fun begins_preparation where
  "begins_preparation (Client_Protocol endpoint index (Reserve_Intent r versions duration)) = True"
| "begins_preparation _ = False"

fun needs_active_native_route where
  "needs_active_native_route (Client_Protocol endpoint index (Reserve_Intent r versions duration)) = True"
| "needs_active_native_route (Client_Protocol endpoint index (Dispatch_Intent r generation versions)) = True"
| "needs_active_native_route (Client_Protocol endpoint index (Source_Intent r generation versions)) = True"
| "needs_active_native_route _ = False"

fun native_client_endpoint where
  "native_client_endpoint (Client_Protocol endpoint index intent) = Some endpoint"
| "native_client_endpoint _ = None"

definition names_prepared_binding where
  "names_prepared_binding s b \<longleftrightarrow> (\<exists>request.
    (lifecycle_phase s = Bound_Cycle request \<or> lifecycle_phase s = Verified_Cycle request \<or>
      (\<exists>cells. lifecycle_phase s = Partial_Cycle request cells)) \<and>
    cycle_session_id request = lifecycle_session s \<and>
    fst (cycle_session_id request) = binding_asset b \<and>
    cycle_binding_id request = prod_encode (binding_key b) \<and> request_flow request = transfer_commit b)"

context integrated_dosp_authority
begin

definition run_predebit_cancellation where
  "run_predebit_cancellation core lease index r =
    (let b = request_binding r; key = binding_key b; origin = fst key;
         m = core_parent core;
         finish = (\<lambda>generation versions.
           if phase_at (machine_state m) key = Some Reservation_Held then Cancel_Intent r generation versions
           else Fence_Intent r generation versions) in
     case lease of
       Live_Lease generation versions \<Rightarrow>
         execute_finality_client (Client_Protocol origin index (finish generation versions)) core
     | Expired_Lease duration \<Rightarrow>
         (case reservation_at (machine_state m) key of
           None \<Rightarrow> (core, Protocol_Response Request_Rejected)
         | Some reservation \<Rightarrow>
             (let assigned = execute_finality_client (Client_Protocol origin index (Reassign_Intent r duration)) core
              in if snd assigned = Protocol_Response Worker_Reassigned then
                   let versions = recorded_versions (core_parent (fst assigned)) key (asset_version (machine_state m));
                       generation = Suc (reservation_generation reservation)
                   in execute_finality_client (Client_Protocol origin index (finish generation versions)) (fst assigned)
                 else (core, Protocol_Response Request_Rejected))))"

definition abort_unexecuted_credit where
  "abort_unexecuted_credit p lease index r released q \<longleftrightarrow>
    (let s = source_lifecycle p; a = source_consensus p; core = credit_core (current_operational a);
         state = machine_state (core_parent core); key = binding_key (request_binding r);
         canceled = run_predebit_cancellation core lease index r in
      if (lifecycle_phase s = Idle_Cycle \<or> names_prepared_binding s (request_binding r)) \<and> cycle_custody s = Local_Cells_Only \<and>
         lifecycle_session s = active_session \<and> binding_asset (request_binding r) = registered_asset (current_operational a) \<and>
         phase_at state key \<in> {Some Reservation_Held, Some Source_Submitted, Some Source_Pending} \<and>
         \<not> source_was_debited state key \<and>
         snd canceled \<in> {Protocol_Response Reservation_Released,Protocol_Response Source_Fenced}
      then released \<and> q = p\<lparr>source_lifecycle := s\<lparr>lifecycle_phase := Idle_Cycle\<rparr>,
        source_consensus := with_finality_core (fst canceled) a\<rparr>
      else \<not> released \<and> q = p)"

lemma aborting_an_unexecuted_binding_never_releases_a_pending_native_debit:
  assumes "cycle_custody (source_lifecycle p) = Native_Debit_Pending key"
  shows "abort_unexecuted_credit p lease index r released q \<longleftrightarrow> \<not> released \<and> q = p"
  using assms by (simp add: abort_unexecuted_credit_def Let_def)

lemma an_actual_source_debit_cannot_be_canceled_as_an_unexecuted_command:
  assumes "source_was_debited (machine_state (core_parent (credit_core (current_operational (source_consensus p)))))
    (binding_key (request_binding r))"
  shows "abort_unexecuted_credit p lease index r released q \<longleftrightarrow> \<not> released \<and> q = p"
  using assms by (simp add: abort_unexecuted_credit_def Let_def)

definition release_live_reversed_debit where
  "release_live_reversed_debit p index r generation versions released q \<longleftrightarrow>
    (let s = source_lifecycle p; a = source_consensus p; core = credit_core (current_operational a);
         b = request_binding r; key = binding_key b;
         native = execute_finality_client (Client_Protocol (fst key) index (Return_Intent r generation versions)) core in
      if names_prepared_binding s b \<and> (\<exists>cycle. lifecycle_phase s = Bound_Cycle cycle \<or> lifecycle_phase s = Verified_Cycle cycle) \<and>
        lifecycle_session s = active_session \<and> binding_asset b = registered_asset (current_operational a) \<and>
        cycle_custody s = Native_Debit_Pending key \<and>
        exact_record_reference core index b Reversed_Decision (request_certificate r) \<and>
        snd native = Protocol_Response Reservation_Released
      then released \<and> q = p\<lparr>source_lifecycle := s\<lparr>cycle_custody := Local_Cells_Only, lifecycle_phase := Idle_Cycle\<rparr>,
        source_consensus := with_finality_core (fst native) a\<rparr>
      else \<not> released \<and> q = p)"

lemma live_reversal_requires_exact_terminal_evidence_and_leaves_billing_unchanged:
  assumes "release_live_reversed_debit p index r generation versions True q"
  shows "exact_record_reference (credit_core (current_operational (source_consensus p))) index
    (request_binding r) Reversed_Decision (request_certificate r) \<and>
    cycle_custody (source_lifecycle q) = Local_Cells_Only \<and>
    lifecycle_invoice (source_lifecycle q) = lifecycle_invoice (source_lifecycle p) \<and>
    lifecycle_cutover (source_lifecycle q) = lifecycle_cutover (source_lifecycle p)"
  using assms by (auto simp: release_live_reversed_debit_def Let_def split: if_splits)

definition native_preparation_ready where
  "native_preparation_ready p command b \<longleftrightarrow>
    (let s = source_lifecycle p; native = current_operational (source_consensus p);
         domains = active_domains (source_recovery p); origin = fst (binding_key b)
     in credit_preparation command \<and> preparation_binding command = Some b \<and>
      lifecycle_session s = active_session \<and> binding_asset b = fst active_session \<and> registered_asset native = binding_asset b \<and>
      (needs_active_native_route command \<longrightarrow>
         recovery_permits_native_credit p \<and> binding_destination b \<in> domains \<and> origin \<in> domains \<and>
         native_client_endpoint command = Some origin \<and>
         legal_at flow_policy (required_level (route_metadata (degree_state native))) (transfer_commit b) \<and>
         level_rank (required_level (route_metadata (degree_state native))) \<le> level_rank (chosen_path (route_metadata (degree_state native)))) \<and>
      (if begins_preparation command then lifecycle_phase s = Idle_Cycle \<and> cycle_custody s = Local_Cells_Only
       else names_prepared_binding s b))"

definition prepare_product_credit where
  "prepare_product_credit p command result q \<longleftrightarrow>
    (\<exists>b updated. native_preparation_ready p command b \<and>
      execute_integrated_client (Prepare_Credit command) (source_consensus p) = (updated, Preparation_Result result) \<and>
      (let state = machine_state (core_parent (credit_core (current_operational updated)));
           exists_debit = phase_at state (binding_key b) = Some Source_Pending \<and> source_was_debited state (binding_key b);
           previous = source_lifecycle p;
           s = (if exists_debit then previous\<lparr>cycle_custody := Native_Debit_Pending (binding_key b)\<rparr> else previous)
       in q = p\<lparr>source_lifecycle := s, source_consensus := updated\<rparr>))"

lemma preparation_cannot_smuggle_an_operation_past_native_admission:
  assumes "prepare_product_credit p command result q"
  shows "credit_preparation command \<and> lifecycle_invoice (source_lifecycle q) = lifecycle_invoice (source_lifecycle p) \<and>
    source_recovery q = source_recovery p \<and>
    committed_cycles (metered_ledger (source_consensus q)) = committed_cycles (metered_ledger (source_consensus p))"
  using assms by (auto simp: prepare_product_credit_def native_preparation_ready_def with_finality_core_def
    with_operational_state_def Let_def split: if_splits)

lemma a_post_reserve_preparation_cannot_change_the_bound_identity:
  assumes "prepare_product_credit p command result q" "\<not> begins_preparation command"
  shows "\<exists>b. preparation_binding command = Some b \<and> names_prepared_binding (source_lifecycle p) b"
proof -
  obtain b where ready: "native_preparation_ready p command b"
    using assms(1) unfolding prepare_product_credit_def by blast
  have binding: "preparation_binding command = Some b \<and> names_prepared_binding (source_lifecycle p) b"
    using ready assms(2) by (simp add: native_preparation_ready_def Let_def)
  then show ?thesis by (rule exI[of _ b])
qed

lemma native_reservation_requires_a_degree_that_permits_commit:
  assumes "prepare_product_credit p (Client_Protocol endpoint index (Reserve_Intent r versions duration)) result q"
  shows "level_rank Coupled \<le> level_rank (required_level (route_metadata (degree_state (current_operational (source_consensus p)))))"
proof -
  obtain b where ready: "native_preparation_ready p (Client_Protocol endpoint index (Reserve_Intent r versions duration)) b"
    using assms unfolding prepare_product_credit_def by blast
  show ?thesis using ready by (simp add: native_preparation_ready_def Let_def)
qed

lemma a_new_native_preparation_waits_for_required_recovery:
  assumes "prepare_product_credit p command result q" "needs_active_native_route command"
  shows "recovery_permits_native_credit p"
proof -
  obtain b where ready: "native_preparation_ready p command b"
    using assms(1) unfolding prepare_product_credit_def by blast
  show ?thesis using ready assms(2) by (simp add: native_preparation_ready_def Let_def)
qed

lemma a_source_preparation_uses_the_exact_active_endpoint:
  assumes "prepare_product_credit p command result q" "needs_active_native_route command"
  shows "\<exists>b. preparation_binding command = Some b \<and> native_client_endpoint command = Some (fst (binding_key b))"
proof -
  obtain b where ready: "native_preparation_ready p command b"
    using assms(1) unfolding prepare_product_credit_def by blast
  show ?thesis by (rule exI[of _ b]) (use ready assms(2) in \<open>simp add: native_preparation_ready_def Let_def\<close>)
qed

definition reassign_pending_product_debit where
  "reassign_pending_product_debit p index r duration accepted q \<longleftrightarrow>
    (let s = source_lifecycle p; a = source_consensus p; native = current_operational a; core = credit_core native;
         b = request_binding r; key = binding_key b;
         worker = execute_finality_client (Client_Protocol (fst key) index (Reassign_Intent r duration)) core in
      if lifecycle_session s = active_session \<and> binding_asset b = registered_asset native \<and>
        names_prepared_binding s b \<and> cycle_custody s = Native_Debit_Pending key \<and>
        native_source_pending native r \<and> source_was_debited (machine_state (core_parent core)) key \<and>
        snd worker = Protocol_Response Worker_Reassigned
      then accepted \<and> q = p\<lparr>source_consensus := with_finality_core (fst worker) a\<rparr>
      else \<not> accepted \<and> q = p)"

lemma a_reassigned_pending_debit_keeps_the_binding_and_both_bills:
  assumes "reassign_pending_product_debit p index r duration accepted q"
  shows "source_lifecycle q = source_lifecycle p \<and> source_recovery q = source_recovery p \<and>
    committed_cycles (metered_ledger (source_consensus q)) = committed_cycles (metered_ledger (source_consensus p))"
  using assms by (auto simp: reassign_pending_product_debit_def Let_def with_finality_core_def with_operational_state_def split: if_splits)

end

end
