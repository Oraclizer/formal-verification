theory Wire_Code_Finite_Closed_Financial
  imports Wire_Code_Finite_Lock_Entry
begin

definition code_finite_closed_current_use :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow> bool" where
  "code_finite_closed_current_use descriptor request \<longleftrightarrow>
    request_authority_epoch request = finite_context_authority_epoch descriptor \<and>
    request_version request = finite_context_version descriptor \<and>
    list_ex (\<lambda>pattern. code_finite_permission_matches pattern (request_caller request) (request_binding request))
      (finite_context_permissions descriptor)"

definition code_finite_closed_footprint :: "code_finite_lock_context \<Rightarrow> transfer_binding \<Rightarrow> nat list" where
  "code_finite_closed_footprint descriptor binding = remdups (binding_asset binding #
    (case map_of (finite_context_dependencies descriptor) (binding_asset binding) of None \<Rightarrow> [] | Some dependencies \<Rightarrow> dependencies))"

definition code_finite_closed_metadata :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow> bool" where
  "code_finite_closed_metadata descriptor request domain =
    (let binding = request_binding request; clear = binding_asset binding \<in> set (finite_context_restriction_clear descriptor)
     in case map_of (finite_context_metadata descriptor) (domain,binding_asset binding) of None \<Rightarrow> False | Some stored \<Rightarrow>
       case binding_operation binding of
         Destination_Credit \<Rightarrow> ordinary_transfer_allowed (code_finite_closed_current_use descriptor request) clear (as_reg_state stored)
       | Ordinary_Transfer_Effect \<Rightarrow> ordinary_transfer_allowed (code_finite_closed_current_use descriptor request) clear (as_reg_state stored)
       | Enforcement_Transfer_Effect kind \<Rightarrow> transfer_allowed (as_reg_state stored)
           \<lparr>transfer_path_value = Authorized_Enforcement kind,baseline_clear = False,
             restriction_clear = clear,enforcement_approved = code_finite_closed_current_use descriptor request\<rparr>
       | Regulatory_State_Effect action \<Rightarrow> False)"

definition code_finite_closed_owns :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> code_finite_financial_state \<Rightarrow> bool" where
  "code_finite_closed_owns descriptor request generation versions financial =
    (code_finite_closed_current_use descriptor request \<and>
      (case map_of (finite_reservations financial) (binding_key (request_binding request)) of None \<Rightarrow> False | Some stored \<Rightarrow>
        reservation_binding stored = request_binding request \<and> reservation_worker stored = request_caller request \<and>
        reservation_generation stored = generation \<and> finite_clock financial < reservation_deadline stored \<and>
        active_reservation_phase (reservation_phase stored) \<and>
        list_all (\<lambda>asset. map_of (finite_asset_owners financial) asset = Some (binding_key (request_binding request)) \<and>
          versions asset = code_finite_nat_default (finite_asset_versions financial) asset) (reservation_footprint stored) \<and>
        list_all (\<lambda>asset. asset \<in> set (code_finite_closed_footprint descriptor (request_binding request))) (reservation_footprint stored) \<and>
        list_all (\<lambda>asset. asset \<in> set (reservation_footprint stored)) (code_finite_closed_footprint descriptor (request_binding request))))"

lemma closed_current_use_is_exactly_the_interpreted_existing_test:
  "code_finite_closed_current_use descriptor request = current_use_allowed (lock_authority (code_interpret_finite_context descriptor)) request"
  by (simp add: code_finite_closed_current_use_def the_finite_current_use_test_consumes_exact_epoch_version_and_explicit_permission_pattern)

lemma closed_footprint_is_exactly_the_interpreted_existing_footprint:
  "code_finite_closed_footprint descriptor binding = required_footprint (code_interpret_finite_context descriptor) binding"
  by (simp add: code_finite_closed_footprint_def required_footprint_def code_interpret_finite_context_def)

lemma closed_metadata_is_exactly_the_interpreted_existing_permission:
  "code_finite_closed_metadata descriptor request domain = metadata_permission (code_interpret_finite_context descriptor) request domain"
  by (cases "map_of (finite_context_metadata descriptor) (domain,binding_asset (request_binding request))";
      cases "binding_operation (request_binding request)")
     (simp_all add: code_finite_closed_metadata_def metadata_permission_def code_interpret_finite_context_def
       code_finite_closed_current_use_def current_use_allowed_def get_reg_state_def get_asset_state_def Let_def)

lemma closed_ownership_is_exactly_the_interpreted_existing_finite_query:
  "code_finite_closed_owns descriptor request generation versions financial =
    code_finite_owns_current (code_interpret_finite_context descriptor) request generation versions financial"
  by (cases "map_of (finite_reservations financial) (binding_key (request_binding request))")
     (auto simp: code_finite_closed_owns_def code_finite_owns_current_def code_finite_owns_recorded_def
       closed_current_use_is_exactly_the_interpreted_existing_test closed_footprint_is_exactly_the_interpreted_existing_footprint
       list_all_iff set_eq_iff)

definition code_finite_closed_reserve :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_closed_reserve descriptor request versions duration machine =
    (let financial = finite_machine_state machine; binding = request_binding request;
         footprint = code_finite_closed_footprint descriptor binding
     in if \<not> code_finite_closed_current_use descriptor request \<or> duration = 0 \<or>
           map_of (finite_reservations financial) (binding_key binding) \<noteq> None \<or>
           list_ex (\<lambda>asset. versions asset \<noteq> code_finite_nat_default (finite_asset_versions financial) asset) footprint
        then code_finite_record_observation request Request_Rejected machine
        else if list_ex (\<lambda>asset. map_of (finite_asset_owners financial) asset \<noteq> None) footprint
        then code_finite_record_observation request Reservation_Busy machine
        else code_finite_record_observation request Reservation_Acquired
          (code_finite_commit_acquired \<lparr>reservation_binding = binding,reservation_footprint = footprint,
            reservation_worker = request_caller request,reservation_generation = 0,
            reservation_deadline = finite_clock financial + duration,reservation_phase = Reservation_Held\<rparr> machine))"

definition code_finite_closed_dispatch :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_closed_dispatch descriptor request generation versions machine =
    (let financial = finite_machine_state machine; binding = request_binding request
     in if code_finite_closed_owns descriptor request generation versions financial \<and>
          map_option reservation_phase (map_of (finite_reservations financial) (binding_key binding)) = Some Reservation_Held \<and>
          binding_operation binding = Destination_Credit \<and> 0 < binding_amount binding \<and>
          binding_amount binding \<le> code_finite_nat_default (finite_source_units financial) (source_account_of binding) \<and>
          code_finite_closed_metadata descriptor request (fst (binding_key binding))
        then code_finite_record_observation request Source_Dispatched (code_finite_commit_dispatched (binding_key binding) machine)
        else code_finite_record_observation request Request_Rejected machine)"

definition code_finite_closed_debit :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_closed_debit descriptor request generation versions machine =
    (let financial = finite_machine_state machine; binding = request_binding request
     in if \<not> code_finite_closed_current_use descriptor request \<or> \<not> code_finite_binding_registered financial binding
        then code_finite_record_observation request Request_Rejected machine
        else if binding_key binding \<in> set (map binding_key (finite_source_effects financial))
        then code_finite_record_observation request Source_Already_Debited machine
        else if code_finite_closed_owns descriptor request generation versions financial \<and>
             map_option reservation_phase (map_of (finite_reservations financial) (binding_key binding))
               \<in> {Some Source_Submitted,Some Source_Pending} \<and>
             binding_operation binding = Destination_Credit \<and> 0 < binding_amount binding \<and>
             binding_amount binding \<le> code_finite_nat_default (finite_source_units financial) (source_account_of binding) \<and>
             finite_context_endpoint descriptor = fst (binding_key binding) \<and>
             code_finite_closed_metadata descriptor request (fst (binding_key binding))
        then code_finite_record_observation request Source_Debited (code_finite_commit_source_effect binding machine)
        else code_finite_record_observation request Request_Rejected machine)"

lemma closed_reserve_is_the_same_finite_reserve_with_the_interpreted_context:
  "code_finite_closed_reserve descriptor request versions duration machine =
    code_finite_acquire_reservation (code_interpret_finite_context descriptor) request versions duration machine"
  by (simp add: code_finite_closed_reserve_def code_finite_acquire_reservation_def Let_def
    closed_current_use_is_exactly_the_interpreted_existing_test closed_footprint_is_exactly_the_interpreted_existing_footprint)

lemma closed_dispatch_is_the_same_finite_dispatch_with_the_interpreted_context:
  "code_finite_closed_dispatch descriptor request generation versions machine =
    code_finite_dispatch_source (code_interpret_finite_context descriptor) request generation versions machine"
  by (simp add: code_finite_closed_dispatch_def code_finite_dispatch_source_def Let_def
    closed_ownership_is_exactly_the_interpreted_existing_finite_query closed_metadata_is_exactly_the_interpreted_existing_permission)

lemma closed_debit_is_the_same_finite_debit_with_the_interpreted_context:
  "code_finite_closed_debit descriptor request generation versions machine =
    code_finite_execute_source_effect (code_interpret_finite_context descriptor) request generation versions machine"
  by (simp add: code_finite_closed_debit_def code_finite_execute_source_effect_def Let_def
    closed_current_use_is_exactly_the_interpreted_existing_test closed_ownership_is_exactly_the_interpreted_existing_finite_query
    closed_metadata_is_exactly_the_interpreted_existing_permission code_interpret_finite_context_def)

datatype code_finite_financial_command = Code_Finite_Reserve nat | Code_Finite_Dispatch nat | Code_Finite_Debit nat

fun code_finite_closed_command :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
  code_finite_financial_command \<Rightarrow> code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_closed_command descriptor request versions (Code_Finite_Reserve duration) machine =
    code_finite_closed_reserve descriptor request (code_model_version_at versions) duration machine"
| "code_finite_closed_command descriptor request versions (Code_Finite_Dispatch generation) machine =
    code_finite_closed_dispatch descriptor request generation (code_model_version_at versions) machine"
| "code_finite_closed_command descriptor request versions (Code_Finite_Debit generation) machine =
    code_finite_closed_debit descriptor request generation (code_model_version_at versions) machine"

theorem each_closed_data_command_is_exactly_its_frozen_financial_operation:
  "map_prod code_interpret_finite_machine id (code_finite_closed_command descriptor request versions command machine) =
    (case command of Code_Finite_Reserve duration \<Rightarrow>
       acquire_reservation (code_interpret_finite_context descriptor) request (vector_lookup versions) duration (code_interpret_finite_machine machine)
     | Code_Finite_Dispatch generation \<Rightarrow>
       dispatch_source (code_interpret_finite_context descriptor) request generation (vector_lookup versions) (code_interpret_finite_machine machine)
     | Code_Finite_Debit generation \<Rightarrow>
       execute_source_effect (code_interpret_finite_context descriptor) request generation (vector_lookup versions) (code_interpret_finite_machine machine))"
proof -
  have lookup: "code_model_version_at versions = vector_lookup versions"
    by (rule ext) (simp add: code_model_version_at_def vector_lookup_def)
  show ?thesis
    by (cases command)
     (simp_all add: closed_reserve_is_the_same_finite_reserve_with_the_interpreted_context
       closed_dispatch_is_the_same_finite_dispatch_with_the_interpreted_context
       closed_debit_is_the_same_finite_debit_with_the_interpreted_context
       the_finite_reserve_and_frozen_reserve_are_exactly_the_same_operation
       the_finite_dispatch_and_frozen_dispatch_are_exactly_the_same_operation
       the_finite_debit_and_frozen_debit_are_exactly_the_same_operation lookup)
qed

text \<open>
  The computational entry constructs no arbitrary infinite Collect value or
  function-valued context. Its total-function interpretation appears only
  on the logical side of the equalities. The exported boundary can accept
  finite data only; the current raw-packet/genesis caller and whole-product
  outcome/commit/control transitions are still separate work. This is an
  exact frozen-operation representation, not a new independent algorithm
  whose agreement is assumed.
\<close>

end
