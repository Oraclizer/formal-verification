theory DOSP_Native_Phases
  imports DOSP_Consensus_Billing
begin

definition current_binding_holds_its_native_lock where
  "current_binding_holds_its_native_lock native r \<longleftrightarrow>
    (let binding = request_binding r;
         state = machine_state (core_parent (credit_core native))
     in current_use_allowed (lock_authority (current_lock_view (credit_core native) (fst (binding_key binding)))) r \<and>
       (\<exists>res. reservation_at state (binding_key binding) = Some res \<and>
       reservation_binding res = binding \<and> reservation_clock state < reservation_deadline res \<and>
       (\<forall>asset \<in> set (reservation_footprint res). asset_owner state asset = Some (binding_key binding))))"

definition native_bind_step where
  "native_bind_step policy grants versions confirmed evidence s native request r reply t \<longleftrightarrow>
     (if degree_state native = lifecycle_cutover s \<and> cycle_names_native_binding request r \<and>
         current_binding_holds_its_native_lock native r
      then lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native)
        (bind_native_custody s native r) (Bind_Cycle request) reply t
      else reply = Precommit_Refused \<and> t = s)"

definition native_verify_step where
  "native_verify_step policy grants versions confirmed evidence s native request index r reply t \<longleftrightarrow>
     (if degree_state native = lifecycle_cutover s \<and> lifecycle_phase s = Bound_Cycle request \<and>
         cycle_names_native_binding request r \<and> current_binding_holds_its_native_lock native r \<and>
         exact_record_reference (credit_core native) index (request_binding r) Confirmed_Decision (request_certificate r)
      then lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native)
        (bind_native_custody s native r) (Verify_Cycle []) reply t
      else reply = Precommit_Refused \<and> t = s)"

lemma native_bind_cannot_pass_without_the_live_exact_lock:
  "\<not> current_binding_holds_its_native_lock native r \<Longrightarrow>
    native_bind_step policy grants versions confirmed evidence s native request r reply t \<longleftrightarrow>
    reply = Precommit_Refused \<and> t = s"
  by (simp add: native_bind_step_def)

lemma native_verification_cannot_pass_without_an_exact_current_confirmation:
  "\<not> exact_record_reference (credit_core native) index (request_binding r) Confirmed_Decision (request_certificate r) \<Longrightarrow>
    native_verify_step policy grants versions confirmed evidence s native request index r reply t \<longleftrightarrow>
    reply = Precommit_Refused \<and> t = s"
  by (simp add: native_verify_step_def)

lemma stale_native_credentials_cannot_bind_or_verify:
  assumes stale: "\<not> current_use_allowed
    (lock_authority (current_lock_view (credit_core native) (fst (binding_key (request_binding r))))) r"
  shows "native_bind_step policy grants versions confirmed evidence s native request r reply t \<longleftrightarrow>
    reply = Precommit_Refused \<and> t = s"
    "native_verify_step policy grants versions confirmed evidence s native request index r reply t \<longleftrightarrow>
    reply = Precommit_Refused \<and> t = s"
  using stale by (simp_all add: native_bind_step_def native_verify_step_def current_binding_holds_its_native_lock_def Let_def)

lemma a_native_verification_retains_cutover_and_invoice:
  assumes "native_verify_step policy grants versions confirmed evidence s native request index r reply t"
  shows "lifecycle_cutover t = lifecycle_cutover s \<and> lifecycle_invoice t = lifecycle_invoice s"
proof (cases "degree_state native = lifecycle_cutover s \<and> lifecycle_phase s = Bound_Cycle request \<and>
         cycle_names_native_binding request r \<and> current_binding_holds_its_native_lock native r \<and>
         exact_record_reference (credit_core native) index (request_binding r) Confirmed_Decision (request_certificate r)")
  case True
  have local: "lifecycle_step policy grants versions confirmed evidence (promotion_locks_clear policy native)
        (bind_native_custody s native r) (Verify_Cycle []) reply t"
    using assms True by (simp add: native_verify_step_def)
  have form: "(\<exists>request. Verify_Cycle [] = Bind_Cycle request) \<or> (\<exists>reports. Verify_Cycle [] = Verify_Cycle reports)"
    by simp
  from lifecycle_preparation_does_not_expose_changes_or_invoice[OF local form] show ?thesis
    by (simp add: bind_native_custody_def split: if_splits)
next
  case False
  with assms show ?thesis by (simp add: native_verify_step_def)
qed

end
