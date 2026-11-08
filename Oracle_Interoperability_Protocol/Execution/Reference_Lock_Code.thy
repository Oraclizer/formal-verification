theory Reference_Lock_Code
  imports "OIP_Reference_Profile.Reference_Lock_Consumption" "Pilot_Debit_Frame"
begin

definition native_debit_current_lease where
  "native_debit_current_lease actor credential cfg request generation versions source \<longleftrightarrow>
    (let state = authoritative_reservation_state source; binding = request_binding request;
         token = credential_token credential in
     request_caller request = actor \<and> current_use_allowed (lock_authority cfg) request \<and>
     token_asset token = binding_asset binding \<and> credential_origin credential = binding_key binding \<and>
     credential_epoch credential = cut_authority_epoch (current_product_cut source) \<and>
     asset_owner state (binding_asset binding) = Some (binding_key binding) \<and>
     (\<exists>reservation. reservation_at state (binding_key binding) = Some reservation \<and>
       reservation_binding reservation = binding \<and> token_owner token = reservation_worker reservation \<and>
       reservation_worker reservation = actor \<and> token_generation token = reservation_generation reservation \<and>
       generation = reservation_generation reservation \<and> reservation_clock state < reservation_deadline reservation \<and>
       active_reservation_phase (reservation_phase reservation) \<and>
       (\<forall>asset \<in> set (reservation_footprint reservation).
          asset_owner state asset = Some (binding_key binding) \<and> versions asset = asset_version state asset) \<and>
       set (reservation_footprint reservation) = set (required_footprint cfg binding)))"

theorem the_native_debit_lease_checks_match_the_model_authority:
  "native_debit_current_lease actor credential cfg request generation versions source \<longleftrightarrow>
    request_caller request = actor \<and> lock_credential_matches actor credential request (Some generation) source \<and>
    owns_current_reservation cfg request generation versions (authoritative_reservation_state source)"
proof -
  let ?binding = "request_binding request"
  let ?state = "authoritative_reservation_state source"
  show ?thesis
    by (cases "reservation_at ?state (binding_key ?binding)")
       (auto simp: native_debit_current_lease_def owns_current_reservation_def owns_recorded_reservation_def
          lock_credential_matches_def product_lock_admitted_def current_lock_token_def
          authoritative_lock_view_def authoritative_lock_token_def current_product_cut_def Let_def)
qed

lemma stale_epoch_and_generation_cannot_pass_the_native_debit_lease:
  assumes "credential_epoch credential \<noteq> cut_authority_epoch (current_product_cut source) \<or>
      token_generation (credential_token credential) \<noteq> generation"
  shows "\<not> native_debit_current_lease actor credential cfg request generation versions source"
  using assms by (auto simp: native_debit_current_lease_def Let_def)

record rust_lock_slot =
  rust_slot_binding :: transfer_binding
  rust_slot_holder :: nat
  rust_slot_generation :: nat
  rust_slot_expires :: nat
  rust_slot_phase :: reservation_phase
  rust_slot_footprint :: "nat set"

record rust_lock_image =
  rust_lock_slots :: "source_key \<Rightarrow> rust_lock_slot option"
  rust_lock_active :: "nat \<Rightarrow> source_key option"
  rust_lock_versions :: "nat \<Rightarrow> nat"
  rust_lock_clock :: nat
  rust_lock_epoch :: nat
  rust_lock_footprint :: "nat set"
  rust_lock_grants :: "(lock_entry \<times> nat) set"
  rust_lock_balance :: nat
  rust_lock_funding :: nat

definition rust_slot_of where
  "rust_slot_of r = \<lparr>rust_slot_binding = reservation_binding r, rust_slot_holder = reservation_worker r,
      rust_slot_generation = reservation_generation r, rust_slot_expires = reservation_deadline r,
      rust_slot_phase = reservation_phase r, rust_slot_footprint = set (reservation_footprint r)\<rparr>"

definition rust_lock_image_matches where
  "rust_lock_image_matches binding other code state \<longleftrightarrow>
    rust_lock_slots code = map_option rust_slot_of \<circ> reservation_at state \<and>
    rust_lock_active code = asset_owner state \<and> rust_lock_versions code = asset_version state \<and>
    rust_lock_clock code = reservation_clock state \<and>
    rust_lock_funding code \<le> rust_lock_balance code \<and>
    source_units state (source_account_of binding) = rust_lock_balance code - rust_lock_funding code + other"

definition rust_bound_debit where
  "rust_bound_debit registered verified entry actor credential binding generation versions code slot \<longleftrightarrow>
    (let token = credential_token credential; asset = binding_asset binding; key = binding_key binding in
      registered \<and> verified \<and> (entry, actor) \<in> rust_lock_grants code \<and>
      token_asset token = asset \<and> credential_origin credential = key \<and> rust_slot_binding slot = binding \<and>
      token_owner token = rust_slot_holder slot \<and> rust_slot_holder slot = actor \<and>
      token_generation token = rust_slot_generation slot \<and> generation = rust_slot_generation slot \<and>
      credential_epoch credential = rust_lock_epoch code \<and> rust_lock_active code asset = Some key \<and>
      rust_slot_footprint slot = rust_lock_footprint code \<and>
      (\<forall>member \<in> rust_slot_footprint slot. rust_lock_active code member = Some key \<and>
        versions member = rust_lock_versions code member))"

definition rust_submit_debit where
  "rust_submit_debit registered verified entry actor credential binding generation versions code =
    (let key = binding_key binding; amount = binding_amount binding in
      case rust_lock_slots code key of None \<Rightarrow> (code, Request_Rejected)
      | Some slot \<Rightarrow>
        if rust_bound_debit registered verified entry actor credential binding generation versions code slot \<and>
           rust_lock_clock code < rust_slot_expires slot \<and> rust_slot_phase slot = Source_Submitted \<and>
           0 < amount \<and> amount \<le> rust_lock_balance code - rust_lock_funding code
        then (code\<lparr>rust_lock_balance := rust_lock_balance code - amount,
          rust_lock_slots := (rust_lock_slots code)(key := Some (slot\<lparr>rust_slot_phase := Source_Pending\<rparr>))\<rparr>, Source_Debited)
        else (code, Request_Rejected))"

theorem rust_debit_consumes_the_related_current_lease_and_matches_state_and_reply:
  fixes code source machine request binding cfg
  defines "binding \<equiv> request_binding request"
    and "machine \<equiv> core_parent (call_authority_state (product_calls source))"
  assumes related: "rust_lock_image_matches binding other code (machine_state machine)"
    and configuration: "rust_lock_footprint code = set (required_footprint cfg binding)"
      "rust_lock_epoch code = cut_authority_epoch (current_product_cut source)"
      "((entry,actor) \<in> rust_lock_grants code) = permitted entry actor command"
    and registered: "request_caller request = actor" "current_use_allowed (lock_authority cfg) request"
    and first: "\<And>reservation. reservation_at (machine_state machine) (binding_key binding) = Some reservation \<Longrightarrow>
      reservation_phase reservation = Source_Submitted \<Longrightarrow>
      \<not> source_was_debited (machine_state machine) (binding_key binding)"
    and operation: "binding_operation binding = Destination_Credit"
    and endpoint: "context_endpoint (lock_authority cfg) = fst (binding_key binding)"
    and metadata: "metadata_permission cfg request (fst (binding_key binding))"
  shows "let native = rust_submit_debit True verified entry actor credential binding generation versions code;
       model = (if verified \<and> permitted entry actor command \<and>
          lock_credential_matches actor credential request (Some generation) source
         then reference_debit_transition cfg request generation versions (rust_lock_balance code) (rust_lock_funding code) machine
         else record_observation request Request_Rejected machine)
    in rust_lock_image_matches binding other (fst native) (machine_state (fst model)) \<and> snd native = snd model"
proof (cases "reservation_at (machine_state machine) (binding_key binding)")
  case None
  then show ?thesis using related
    by (auto simp: rust_lock_image_matches_def rust_submit_debit_def reference_debit_transition_def
        record_observation_def Let_def binding_def)
next
  case (Some slot)
  let ?state = "machine_state machine"
  let ?amount = "binding_amount binding"
  let ?gate = "verified \<and> permitted entry actor command \<and>
    lock_credential_matches actor credential request (Some generation) source"
  let ?effect = "?gate \<and> owns_current_reservation cfg request generation versions ?state \<and>
    reservation_phase slot = Source_Submitted \<and> 0 < ?amount \<and>
    ?amount \<le> rust_lock_balance code - rust_lock_funding code"
  have code_slot: "rust_lock_slots code (binding_key binding) = Some (rust_slot_of slot)"
    using related Some by (simp add: rust_lock_image_matches_def)
  have model_slot: "reservation_at (authoritative_reservation_state source) (binding_key binding) = Some slot"
    using Some by (simp add: authoritative_reservation_state_def machine_def)
  have state: "authoritative_reservation_state source = ?state"
    by (simp add: authoritative_reservation_state_def machine_def)
  have clock: "rust_lock_clock code = reservation_clock ?state" and owners: "rust_lock_active code = asset_owner ?state"
    and versions: "rust_lock_versions code = asset_version ?state"
    and funds: "rust_lock_funding code \<le> rust_lock_balance code"
    and balance: "source_units ?state (source_account_of binding) = rust_lock_balance code - rust_lock_funding code + other"
    using related by (simp_all add: rust_lock_image_matches_def)
  have lease: "native_debit_current_lease actor credential cfg request generation versions source =
      (lock_credential_matches actor credential request (Some generation) source \<and>
       owns_current_reservation cfg request generation versions ?state)"
    using the_native_debit_lease_checks_match_the_model_authority[of actor credential cfg request generation versions source]
      registered(1) state by simp
  have raw_lease: "(rust_bound_debit True verified entry actor credential binding generation versions code (rust_slot_of slot) \<and>
      rust_lock_clock code < rust_slot_expires (rust_slot_of slot) \<and> active_reservation_phase (rust_slot_phase (rust_slot_of slot))) =
      (verified \<and> permitted entry actor command \<and> native_debit_current_lease actor credential cfg request generation versions source)"
    using model_slot configuration registered owners versions clock state
    by (simp add: rust_bound_debit_def rust_slot_of_def native_debit_current_lease_def Let_def binding_def; blast)
  have exact_gate: "(rust_bound_debit True verified entry actor credential binding generation versions code (rust_slot_of slot) \<and>
      rust_lock_clock code < rust_slot_expires (rust_slot_of slot) \<and> rust_slot_phase (rust_slot_of slot) = Source_Submitted \<and>
      0 < ?amount \<and> ?amount \<le> rust_lock_balance code - rust_lock_funding code) = ?effect"
    using raw_lease lease by (cases "reservation_phase slot = Source_Submitted") (auto simp: rust_slot_of_def)
  have enough: "?amount \<le> rust_lock_balance code - rust_lock_funding code \<Longrightarrow>
      ?amount \<le> source_units ?state (source_account_of binding)"
    using balance by arith
  have bound: "owns_current_reservation cfg request generation versions ?state \<Longrightarrow> binding_is_registered ?state binding"
    by (auto simp: owns_current_reservation_def owns_recorded_reservation_def binding_is_registered_def binding_def)
  have compute: "execute_source_effect cfg request generation versions machine =
      (if owns_current_reservation cfg request generation versions ?state
       then record_observation request Source_Debited (commit_reservation_event (Source_Effect_Event binding) machine)
       else record_observation request Request_Rejected machine)"
    if phase: "reservation_phase slot = Source_Submitted" and amount: "0 < ?amount"
      "?amount \<le> rust_lock_balance code - rust_lock_funding code"
    using Some phase amount(1) enough[OF amount(2)] registered(2) first[OF Some phase] operation endpoint metadata bound
    by (cases "owns_current_reservation cfg request generation versions ?state")
       (simp_all add: execute_source_effect_def phase_at_def Let_def binding_def)
  have model: "(if ?gate then reference_debit_transition cfg request generation versions (rust_lock_balance code)
      (rust_lock_funding code) machine else record_observation request Request_Rejected machine) =
    (if ?effect then record_observation request Source_Debited (commit_reservation_event (Source_Effect_Event binding) machine)
      else record_observation request Request_Rejected machine)"
    using Some compute
    by (auto simp: reference_debit_transition_def owns_current_reservation_def owns_recorded_reservation_def
        Let_def binding_def split: if_splits)
  have subtract: "?effect \<Longrightarrow> rust_lock_balance code - rust_lock_funding code + other - ?amount =
      rust_lock_balance code - ?amount - rust_lock_funding code + other"
    using funds by arith
  have result: "rust_lock_image_matches binding other
      (fst (rust_submit_debit True verified entry actor credential binding generation versions code))
      (machine_state (fst (if ?gate then reference_debit_transition cfg request generation versions
         (rust_lock_balance code) (rust_lock_funding code) machine
       else record_observation request Request_Rejected machine))) \<and>
      snd (rust_submit_debit True verified entry actor credential binding generation versions code) =
      snd (if ?gate then reference_debit_transition cfg request generation versions
        (rust_lock_balance code) (rust_lock_funding code) machine
       else record_observation request Request_Rejected machine)"
  proof (cases ?effect)
    case True
    then show ?thesis using related Some code_slot exact_gate model subtract[OF True]
      by (auto simp: rust_submit_debit_def rust_lock_image_matches_def rust_slot_of_def
          commit_reservation_event_def record_observation_def set_phase_def Let_def fun_eq_iff)
  next
    case False
    have disabled: "\<not> (rust_bound_debit True verified entry actor credential binding generation versions code (rust_slot_of slot) \<and>
      rust_lock_clock code < rust_slot_expires (rust_slot_of slot) \<and> rust_slot_phase (rust_slot_of slot) = Source_Submitted \<and>
      0 < ?amount \<and> ?amount \<le> rust_lock_balance code - rust_lock_funding code)"
      using False exact_gate by blast
    have rejected: "rust_submit_debit True verified entry actor credential binding generation versions code = (code,Request_Rejected)"
      using disabled code_slot by (simp add: rust_submit_debit_def Let_def)
    have unmodified: "(if ?gate then reference_debit_transition cfg request generation versions (rust_lock_balance code)
       (rust_lock_funding code) machine else record_observation request Request_Rejected machine) =
      record_observation request Request_Rejected machine"
      using model False by (simp only: if_not_P if_False)
    show ?thesis using related by (simp add: rejected unmodified record_observation_def)
  qed
  then show ?thesis by (simp add: Let_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_native_debit_lease_checks_match_the_model_authority
      stale_epoch_and_generation_cannot_pass_the_native_debit_lease
      rust_debit_consumes_the_related_current_lease_and_matches_state_and_reply})
  then () else error "Unexpected oracle in native Debit lease correspondence"
\<close>

end
