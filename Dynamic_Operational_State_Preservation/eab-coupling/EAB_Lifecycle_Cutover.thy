theory EAB_Lifecycle_Cutover
  imports EAB_Binding_Cutover
begin

fun resolution_decision :: "pending_resolution \<Rightarrow> terminal_kind" where
  "resolution_decision Reconcile_Credit = Confirmed_Decision"
| "resolution_decision Release_Reversal = Reversed_Decision"

fun resolution_intent :: "pending_resolution \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  version_vector \<Rightarrow> protocol_intent" where
  "resolution_intent Reconcile_Credit r generation versions = Reconcile_Intent r generation versions"
| "resolution_intent Release_Reversal r generation versions = Return_Intent r generation versions"

fun reservation_outcome :: "finality_reply \<Rightarrow> reservation_reply" where
  "reservation_outcome (Protocol_Response reply) = reply"
| "reservation_outcome _ = Request_Rejected"

definition recorded_versions ::
  "reservation_machine \<Rightarrow> source_key \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> version_vector"
where
  "recorded_versions m key versions =
    (case reservation_at (machine_state m) key of
       None \<Rightarrow> []
     | Some res \<Rightarrow> map (\<lambda>asset. (asset, versions asset)) (reservation_footprint res))"

lemma vector_lookup_in_recorded_footprint:
  assumes "asset \<in> set footprint"
  shows "vector_lookup (map (\<lambda>a. (a, versions a)) footprint) asset = versions asset"
  using assms by (induction footprint) (auto simp: vector_lookup_def)

lemma recorded_vector_preserves_lease_check:
  "owns_recorded_reservation c r generation
      (vector_lookup (recorded_versions m (binding_key (request_binding r)) versions)) (machine_state m) =
    owns_recorded_reservation c r generation versions (machine_state m)"
  by (cases "reservation_at (machine_state m) (binding_key (request_binding r))")
    (auto simp: owns_recorded_reservation_def recorded_versions_def vector_lookup_in_recorded_footprint)

context source_attestation
begin

definition lock_resolution_word ::
  "pending_resolution \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow> nat
    \<Rightarrow> finality_core \<Rightarrow> finality_operation list"
where
  "lock_resolution_word mode epoch index r duration core =
    (let key = binding_key (request_binding r); origin = fst key; m = core_parent core in
      case reservation_at (machine_state m) key of
        None \<Rightarrow> []
      | Some res \<Rightarrow>
          let acquire = Invoke_Protocol origin epoch index (Reassign_Intent r duration)
          in if snd (core_result acquire core) = Protocol_Response Worker_Reassigned then
              let assigned = finality_step acquire core;
                  versions = recorded_versions (core_parent assigned) key (asset_version (machine_state m));
                  release = Invoke_Protocol origin (core_epoch assigned) index
                    (resolution_intent mode r (Suc (reservation_generation res)) versions)
              in [acquire, release]
             else [acquire])"

definition execute_lock_word ::
  "finality_operation list \<Rightarrow> finality_core \<Rightarrow> finality_core \<times> reservation_reply"
where
  "execute_lock_word word core =
    (run_finality word core,
      if word = [] then Request_Rejected
      else reservation_outcome (snd (core_result (last word) (run_finality (butlast word) core))))"

lemma native_intent_projects_to_the_recorded_cleanup:
  "intent_result c (resolution_intent mode r generation
      (recorded_versions m (binding_key (request_binding r)) versions)) m =
    lift_protocol_result (case mode of
      Reconcile_Credit \<Rightarrow> reconcile_recorded_credit c r generation versions m
    | Release_Reversal \<Rightarrow> release_to_source c r generation versions m)"
  by (cases mode)
    (simp_all add: reconcile_recorded_credit_def release_to_source_def recorded_vector_preserves_lease_check)

lemma native_lock_word_projects_to_the_lease_calls:
  fixes mode :: pending_resolution and epoch index duration :: nat and r :: execution_request and core :: finality_core
  assumes epoch: "epoch = core_epoch core"
    and exact: "exact_record_reference core index (request_binding r)
      (resolution_decision mode) (request_certificate r)"
  defines "word \<equiv> lock_resolution_word mode epoch index r duration core"
  shows "(core_parent (fst (execute_lock_word word core)), snd (execute_lock_word word core)) =
    settle_expired_reservation mode (current_lock_view core (fst (binding_key (request_binding r)))) r duration
      (core_parent core)"
proof (cases "reservation_at (machine_state (core_parent core)) (binding_key (request_binding r))")
  case None
  then show ?thesis
    by (simp add: word_def lock_resolution_word_def execute_lock_word_def settle_expired_reservation_def Let_def)
next
  case (Some res)
  let ?key = "binding_key (request_binding r)"
  let ?m = "core_parent core"
  let ?view = "current_lock_view core (fst ?key)"
  let ?acquire = "Invoke_Protocol (fst ?key) epoch index (Reassign_Intent r duration)"
  let ?taken = "reassign_worker ?view r duration ?m"
  let ?assigned = "finality_step ?acquire core"
  let ?generation = "Suc (reservation_generation res)"
  let ?versions = "asset_version (machine_state ?m)"
  let ?intent = "resolution_intent mode r ?generation (recorded_versions (fst ?taken) ?key ?versions)"
  let ?finish = "Invoke_Protocol (fst ?key) (Suc (core_epoch core)) index ?intent"
  let ?cleanup = "case mode of Reconcile_Credit \<Rightarrow>
      reconcile_recorded_credit ?view r ?generation ?versions (fst ?taken)
    | Release_Reversal \<Rightarrow> release_to_source ?view r ?generation ?versions (fst ?taken)"
  have acquire: "invoke_protocol (fst ?key) epoch index (Reassign_Intent r duration) core =
      (core\<lparr>core_parent := fst ?taken\<rparr>, Protocol_Response (snd ?taken))"
    using epoch by (simp add: invoke_protocol_def lift_protocol_result_def Let_def)
  have parent: "core_parent ?assigned = fst ?taken"
    and view: "current_lock_view ?assigned (fst ?key) = ?view"
    and records: "core_records ?assigned = core_records core"
    by (simp_all add: finality_step_def acquire current_lock_view_def)
  have guard: "terminal_intent_guard ?assigned index ?intent"
    using exact records by (cases mode) (simp_all add: exact_record_reference_def record_reference_def)
  have cleanup: "intent_result ?view ?intent (fst ?taken) = lift_protocol_result ?cleanup"
    by (rule native_intent_projects_to_the_recorded_cleanup)
  have release: "invoke_protocol (fst ?key) (Suc (core_epoch core)) index ?intent ?assigned =
      (?assigned\<lparr>core_parent := fst ?cleanup\<rparr>, Protocol_Response (snd ?cleanup))"
    using guard by (simp add: invoke_protocol_def parent view cleanup lift_protocol_result_def Let_def)
  have step_result: "core_result ?finish ?assigned =
      (?assigned\<lparr>core_parent := fst ?cleanup\<rparr>, Protocol_Response (snd ?cleanup))"
    by (simp only: core_result.simps release)
  have result_value: "fst (core_result ?finish ?assigned) = ?assigned\<lparr>core_parent := fst ?cleanup\<rparr>"
    using step_result by (metis fst_conv)
  have stepped: "finality_step ?finish ?assigned =
      (fst (core_result ?finish ?assigned))\<lparr>core_epoch := Suc (core_epoch ?assigned)\<rparr>"
    by (rule finality_step_def)
  have final: "finality_step ?finish ?assigned =
      (?assigned\<lparr>core_parent := fst ?cleanup\<rparr>)\<lparr>core_epoch := Suc (core_epoch ?assigned)\<rparr>"
    by (simp only: stepped result_value)
  have released_parent: "core_parent (finality_step ?finish ?assigned) = fst ?cleanup"
    unfolding final by simp
  show ?thesis using Some
    by (cases "snd ?taken = Worker_Reassigned")
      (simp_all add: word_def lock_resolution_word_def execute_lock_word_def settle_expired_reservation_def
        acquire parent release released_parent Let_def)
qed

lemma lock_word_preserves_published_records:
  "core_published (run_finality (lock_resolution_word mode epoch index r duration core) core) = core_published core"
  "core_records (run_finality (lock_resolution_word mode epoch index r duration core) core) = core_records core"
  by (auto simp: lock_resolution_word_def finality_step_def invoke_protocol_def reject_protocol_intent_def Let_def
      split: option.splits if_splits)

definition resolve_cutover_lock ::
  "pending_resolution \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
    metered_source_state \<Rightarrow> metered_source_state \<times> reservation_reply"
where
  "resolve_cutover_lock mode epoch index r duration s =
    (let b = request_binding r; core = credit_core s in
      if binding_asset b = registered_asset s \<and> epoch = core_epoch core \<and>
        exact_record_reference core index b (resolution_decision mode) (request_certificate r)
      then let settled = execute_lock_word (lock_resolution_word mode epoch index r duration core) core
           in (s\<lparr>source_authority := (source_authority s)
                 \<lparr>terminal_authority := fst settled\<rparr>\<rparr>, snd settled)
      else (s, Request_Rejected))"

lemma accepted_lock_resolution_runs_the_native_eab_word:
  assumes "resolve_cutover_lock mode epoch index r duration s = (t, Reservation_Released)"
  shows "credit_core t =
    run_finality (lock_resolution_word mode epoch index r duration (credit_core s)) (credit_core s)"
  using assms by (auto simp: resolve_cutover_lock_def execute_lock_word_def Let_def split: if_splits)

lemma lock_resolution_keeps_the_cutover_and_durable_publication:
  assumes "resolve_cutover_lock mode epoch index r duration s = (t, reply)"
  shows "degree_state t = degree_state s \<and>
    publication_slots (source_authority t) = publication_slots (source_authority s) \<and>
    core_published (credit_core t) = core_published (credit_core s) \<and>
    core_records (credit_core t) = core_records (credit_core s)"
  using assms by (auto simp: resolve_cutover_lock_def execute_lock_word_def lock_word_preserves_published_records
      Let_def split: if_splits)

lemma stale_lifecycle_request_cannot_take_over_or_release:
  assumes "epoch \<noteq> core_epoch (credit_core s)"
  shows "resolve_cutover_lock mode epoch index r duration s = (s, Request_Rejected)"
  using assms by (simp add: resolve_cutover_lock_def Let_def)

theorem current_terminal_evidence_clears_the_scope_of_the_old_lock:
  fixes r :: execution_request and s :: metered_source_state and b :: transfer_binding
    and c :: lock_context and m :: reservation_machine
  defines "b \<equiv> request_binding r"
    and "c \<equiv> current_lock_view (credit_core s) (fst (binding_key b))"
    and "m \<equiv> core_parent (credit_core s)"
  assumes scoped: "binding_asset b = registered_asset s"
    and epoch: "epoch = core_epoch (credit_core s)"
    and reference: "exact_record_reference (credit_core s) index b (resolution_decision mode) (request_certificate r)"
    and ownership: "ownership_consistent (machine_state m)"
    and at: "reservation_at (machine_state m) (binding_key b) = Some res"
    and current: "current_use_allowed (lock_authority c) r"
    and duration: "duration > 0"
    and binding: "reservation_binding res = b"
    and pending: "reservation_phase res = Source_Pending"
    and expired: "reservation_deadline res \<le> reservation_clock (machine_state m)"
    and evidence: "case mode of Reconcile_Credit \<Rightarrow> b \<in> set (credit_history (received_messages (machine_state m)))
      | Release_Reversal \<Rightarrow> reversed_source_evidence (lock_authority c) r (machine_state m)"
  defines "released \<equiv> resolve_cutover_lock mode epoch index r duration s"
  shows "snd released = Reservation_Released \<and>
    (\<forall>asset. asset_owner (machine_state (core_parent (credit_core (fst released)))) asset
      \<noteq> Some (binding_key b)) \<and>
    degree_state (fst released) = degree_state s"
proof -
  have post: "snd (settle_expired_reservation mode c r duration m) = Reservation_Released \<and>
    (\<forall>asset. asset_owner (machine_state (fst (settle_expired_reservation mode c r duration m))) asset
      \<noteq> Some (binding_key b))"
    unfolding b_def
    by (rule settle_expired_reservation_releases_its_actual_lock
      [OF ownership at[unfolded b_def] current duration binding[unfolded b_def] pending expired evidence[unfolded b_def]])
  let ?native = "execute_lock_word (lock_resolution_word mode epoch index r duration (credit_core s)) (credit_core s)"
  have projection: "(core_parent (fst ?native), snd ?native) = settle_expired_reservation mode c r duration m"
    using native_lock_word_projects_to_the_lease_calls[OF epoch reference[unfolded b_def]]
    by (simp add: m_def c_def b_def)
  have result: "released =
    (s\<lparr>source_authority := (source_authority s)\<lparr>terminal_authority := fst ?native\<rparr>\<rparr>, snd ?native)"
    using scoped epoch reference by (simp add: released_def resolve_cutover_lock_def b_def Let_def)
  from projection have "core_parent (fst ?native) = fst (settle_expired_reservation mode c r duration m)"
    "snd ?native = snd (settle_expired_reservation mode c r duration m)" by (metis fst_conv snd_conv)+
  with result post show ?thesis by simp
qed

theorem resolved_promotion_preserves_past_charges_and_meters_the_new_policy:
  assumes first: "meter_source_credit policy old_ticket old_epoch old_index old_sequence route old_request s =
      (charged, Credit_Metered old_entry)"
    and release: "resolve_cutover_lock mode release_epoch release_index old_request duration charged =
      (released, Reservation_Released)"
    and promote: "promote_settled_asset policy grants epoch version released =
      (promoted, transition_result.Accepted Promotion_Finalized)"
    and second: "meter_source_credit policy new_ticket new_epoch new_index new_sequence route new_request promoted =
      (t, Credit_Metered new_entry)"
  shows "billing_history (degree_state t) = billing_history (degree_state s) @ [old_entry, new_entry] \<and>
    billing_level old_entry = Coupled \<and> billing_level new_entry = Atomic \<and>
    billing_epoch new_entry = epoch \<and> billing_version new_entry = version"
proof -
  have first_step: "cutover_step policy grants (degree_state s)
      (Commit_Binding (prod_encode (binding_key (request_binding old_request))) old_ticket
        (fst (binding_key (request_binding old_request))) (binding_destination (request_binding old_request))
        (binding_amount (request_binding old_request)) True)
      (transition_result.Accepted Binding_Committed) (degree_state charged)"
    and old_entry: "old_entry = billing_record (prod_encode (binding_key (request_binding old_request)))
      (route_metadata (degree_state s)) (transfer_commit (request_binding old_request))"
    and old_history: "billing_history (degree_state charged) = billing_history (degree_state s) @ [old_entry]"
    using metered_credit_projects_to_one_cutover_commit[OF first, where grants=grants] by blast+
  have released_view: "degree_state released = degree_state charged"
    using lock_resolution_keeps_the_cutover_and_durable_publication[OF release] by blast
  have cutover: "cutover_step policy grants (degree_state released) (Confirm_Promotion epoch version)
    (transition_result.Accepted Promotion_Finalized) (degree_state promoted)"
    using settled_asset_promotion_projects_to_cutover[OF promote] by blast
  have left: "required_level (route_metadata (degree_state s)) = Coupled"
    using accepted_promotion_has_one_metadata_boundary[OF cutover]
      commit_adds_one_required_level_bill[OF first_step] released_view by simp
  show ?thesis
    using accepted_promotion_has_one_metadata_boundary[OF cutover]
      metered_credit_projects_to_one_cutover_commit[OF second, where grants=grants]
      released_view left old_entry old_history
    by (simp add: billing_record_def promoted_metadata_def)
qed

end

end
