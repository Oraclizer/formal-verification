theory Wire_Code_Finite_Lock_Entry
  imports Wire_Code_Finite_Context
begin

definition code_finite_claim_assets :: "nat list \<Rightarrow> source_key \<Rightarrow> (nat \<times> source_key) list \<Rightarrow> (nat \<times> source_key) list" where
  "code_finite_claim_assets footprint key rows = fold (\<lambda>asset. code_finite_put asset key) footprint rows"

lemma finite_asset_claims_are_the_exact_existing_footprint_override:
  "map_of (code_finite_claim_assets footprint key rows) =
    (\<lambda>asset. if asset \<in> set footprint then Some key else map_of rows asset)"
  by (induction footprint arbitrary: rows)
     (auto simp: code_finite_claim_assets_def finite_put_is_exactly_a_total_map_some_update fun_eq_iff)

definition code_finite_acquired :: "asset_reservation \<Rightarrow> code_finite_financial_state \<Rightarrow> code_finite_financial_state" where
  "code_finite_acquired stored financial = financial\<lparr>
    finite_reservations := code_finite_put (binding_key (reservation_binding stored)) stored (finite_reservations financial),
    finite_asset_owners := code_finite_claim_assets (reservation_footprint stored) (binding_key (reservation_binding stored))
      (finite_asset_owners financial)\<rparr>"

definition code_finite_commit_acquired :: "asset_reservation \<Rightarrow> code_finite_reservation_machine \<Rightarrow> code_finite_reservation_machine" where
  "code_finite_commit_acquired stored machine = machine\<lparr>
    finite_machine_state := code_finite_acquired stored (finite_machine_state machine),
    finite_machine_journal := finite_machine_journal machine @ [Acquired_Event stored]\<rparr>"

definition code_finite_commit_dispatched :: "source_key \<Rightarrow> code_finite_reservation_machine \<Rightarrow> code_finite_reservation_machine" where
  "code_finite_commit_dispatched key machine = machine\<lparr>
    finite_machine_state := code_finite_set_phase key Source_Submitted (finite_machine_state machine),
    finite_machine_journal := finite_machine_journal machine @ [Dispatched_Event key]\<rparr>"

lemma finite_acquire_event_interprets_the_exact_existing_reservation_and_footprint:
  "code_interpret_finite_financial (code_finite_acquired stored financial) =
    apply_reservation_event (Acquired_Event stored) (code_interpret_finite_financial financial)"
  by (simp add: code_finite_acquired_def code_interpret_finite_financial_def
    finite_put_is_exactly_a_total_map_some_update finite_asset_claims_are_the_exact_existing_footprint_override;
      rule ext; simp split: if_splits)

lemma finite_acquire_commit_interprets_the_exact_existing_state_and_event:
  "code_interpret_finite_machine (code_finite_commit_acquired stored machine) =
    commit_reservation_event (Acquired_Event stored) (code_interpret_finite_machine machine)"
  by (simp add: code_finite_commit_acquired_def code_interpret_finite_machine_def commit_reservation_event_def
    finite_acquire_event_interprets_the_exact_existing_reservation_and_footprint)

lemma finite_dispatch_commit_interprets_the_exact_existing_state_and_event:
  "code_interpret_finite_machine (code_finite_commit_dispatched key machine) =
    commit_reservation_event (Dispatched_Event key) (code_interpret_finite_machine machine)"
  by (simp add: code_finite_commit_dispatched_def code_interpret_finite_machine_def commit_reservation_event_def
    finite_phase_update_interprets_the_same_frozen_phase_update)

definition code_finite_acquire_reservation :: "lock_context \<Rightarrow> execution_request \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> code_finite_reservation_machine \<Rightarrow>
  (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_acquire_reservation authority_view request versions duration machine =
    (let financial = finite_machine_state machine; binding = request_binding request;
         footprint = required_footprint authority_view binding
     in if \<not> current_use_allowed (lock_authority authority_view) request \<or> duration = 0 \<or>
           map_of (finite_reservations financial) (binding_key binding) \<noteq> None \<or>
           list_ex (\<lambda>asset. versions asset \<noteq> code_finite_nat_default (finite_asset_versions financial) asset) footprint
        then code_finite_record_observation request Request_Rejected machine
        else if list_ex (\<lambda>asset. map_of (finite_asset_owners financial) asset \<noteq> None) footprint
        then code_finite_record_observation request Reservation_Busy machine
        else code_finite_record_observation request Reservation_Acquired
          (code_finite_commit_acquired \<lparr>reservation_binding = binding,reservation_footprint = footprint,
            reservation_worker = request_caller request,reservation_generation = 0,
            reservation_deadline = finite_clock financial + duration,reservation_phase = Reservation_Held\<rparr> machine))"

theorem the_finite_reserve_and_frozen_reserve_are_exactly_the_same_operation:
  "map_prod code_interpret_finite_machine id
      (code_finite_acquire_reservation authority_view request versions duration machine) =
    acquire_reservation authority_view request versions duration (code_interpret_finite_machine machine)"
proof -
  let ?financial = "finite_machine_state machine"
  let ?state = "machine_state (code_interpret_finite_machine machine)"
  let ?binding = "request_binding request"
  let ?footprint = "required_footprint authority_view ?binding"
  have reserved: "map_of (finite_reservations ?financial) (binding_key ?binding) = reservation_at ?state (binding_key ?binding)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def)
  have versions: "list_ex (\<lambda>asset. versions asset \<noteq> code_finite_nat_default (finite_asset_versions ?financial) asset) ?footprint =
      (\<exists>asset \<in> set ?footprint. versions asset \<noteq> asset_version ?state asset)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def list_ex_iff)
  have busy: "list_ex (\<lambda>asset. map_of (finite_asset_owners ?financial) asset \<noteq> None) ?footprint =
      (\<exists>asset \<in> set ?footprint. asset_owner ?state asset \<noteq> None)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def list_ex_iff)
  have clock: "finite_clock ?financial = reservation_clock ?state"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def)
  show ?thesis
    unfolding code_finite_acquire_reservation_def acquire_reservation_def Let_def
    by (simp only: reserved versions busy clock;
        simp add: finite_observation_interprets_the_same_complete_existing_observation
          finite_acquire_commit_interprets_the_exact_existing_state_and_event split: if_splits)
qed

definition code_finite_dispatch_source :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_dispatch_source authority_view request generation versions machine =
    (let financial = finite_machine_state machine; binding = request_binding request
     in if code_finite_owns_current authority_view request generation versions financial \<and>
          map_option reservation_phase (map_of (finite_reservations financial) (binding_key binding)) = Some Reservation_Held \<and>
          binding_operation binding = Destination_Credit \<and> 0 < binding_amount binding \<and>
          binding_amount binding \<le> code_finite_nat_default (finite_source_units financial) (source_account_of binding) \<and>
          metadata_permission authority_view request (fst (binding_key binding))
        then code_finite_record_observation request Source_Dispatched (code_finite_commit_dispatched (binding_key binding) machine)
        else code_finite_record_observation request Request_Rejected machine)"

theorem the_finite_dispatch_and_frozen_dispatch_are_exactly_the_same_operation:
  "map_prod code_interpret_finite_machine id
      (code_finite_dispatch_source authority_view request generation versions machine) =
    dispatch_source authority_view request generation versions (code_interpret_finite_machine machine)"
proof -
  let ?financial = "finite_machine_state machine"
  let ?state = "machine_state (code_interpret_finite_machine machine)"
  let ?binding = "request_binding request"
  have ownership: "code_finite_owns_current authority_view request generation versions ?financial =
      owns_current_reservation authority_view request generation versions ?state"
    by (simp add: code_interpret_finite_machine_def finite_current_ownership_is_the_exact_existing_current_footprint_test)
  have phase: "map_option reservation_phase (map_of (finite_reservations ?financial) (binding_key ?binding)) = phase_at ?state (binding_key ?binding)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def phase_at_def)
  have balance: "code_finite_nat_default (finite_source_units ?financial) (source_account_of ?binding) = source_units ?state (source_account_of ?binding)"
    by (simp add: code_interpret_finite_machine_def code_interpret_finite_financial_def)
  show ?thesis
    unfolding code_finite_dispatch_source_def dispatch_source_def Let_def
    by (simp only: ownership phase balance;
        simp add: finite_observation_interprets_the_same_complete_existing_observation
          finite_dispatch_commit_interprets_the_exact_existing_state_and_event split: if_splits)
qed

text \<open>
  These Reserve and Dispatch functions are finite representations of the
  corresponding frozen financial operations. Their interpretation keeps
  every failure/busy branch, journal and observation. Source current identity,
  route/operation grants, credential and exact source-owner checks are
  separate consumers; the pooled old Dispatch predicate is not silently
  asserted to distinguish a source payer absent from transfer_binding.
\<close>

end
