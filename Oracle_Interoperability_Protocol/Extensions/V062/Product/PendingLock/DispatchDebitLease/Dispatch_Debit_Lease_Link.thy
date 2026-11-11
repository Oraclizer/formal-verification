theory Dispatch_Debit_Lease_Link
  imports "OIP_Reserve_Debit_Finite_Base.Wire_Code_Finite_Integer_ABI"
    "OIP_Reference_Execution.Reference_Lock_Code" "HOL-Library.Code_Target_Nat"
begin

text \<open>Single-reservation typed Ledger clock fixtures. The existing
finite seed supplies the model-only ACTIVE metadata, restriction clearance
and version coordinates. The reservation, active owner, versions, payer,
funding and clock are supplied before the step. Journal and observation
prefixes have no output in this interface.\<close>

definition ddl_binding where
  "ddl_binding ddl_epoch ddl_separator ddl_words =
    (case ddl_words of [ddl_src,ddl_event,ddl_asset,ddl_owner,ddl_dst,ddl_recipient,ddl_amount] \<Rightarrow>
      Some \<lparr>binding_key = (ddl_src,ddl_event), binding_asset = ddl_asset, binding_amount = ddl_amount,
        binding_destination = ddl_dst, binding_recipient = ddl_recipient, binding_source_epoch = ddl_epoch,
        binding_operation = Destination_Credit, binding_separator = ddl_separator\<rparr>
    | _ \<Rightarrow> None)"

definition ddl_credential where
  "ddl_credential ddl_words =
    (case ddl_words of [ddl_asset,ddl_src,ddl_event,ddl_holder,ddl_gen,ddl_epoch] \<Rightarrow>
       Some \<lparr>credential_token = \<lparr>token_asset = ddl_asset, token_owner = ddl_holder,
           token_generation = ddl_gen\<rparr>, credential_epoch = ddl_epoch, credential_origin = (ddl_src,ddl_event)\<rparr>
     | _ \<Rightarrow> None)"

definition ddl_request where
  "ddl_request ddl_binding_value ddl_actor ddl_epoch ddl_version =
    \<lparr>request_binding = ddl_binding_value,
      request_certificate = \<lparr>certificate_statement = \<lparr>statement_binding = ddl_binding_value,
          statement_status = Observed\<rparr>, certificate_epoch = ddl_epoch,
        certificate_signers = [], certificate_signature = 0\<rparr>,
      request_caller = ddl_actor, request_authority_epoch = ddl_epoch, request_version = ddl_version\<rparr>"

definition ddl_rust_image where
  "ddl_rust_image ddl_financial ddl_footprint ddl_epoch ddl_actor ddl_granted ddl_balance ddl_funding =
    \<lparr>rust_lock_slots = map_option rust_slot_of \<circ> map_of (finite_reservations ddl_financial),
      rust_lock_active = map_of (finite_asset_owners ddl_financial),
      rust_lock_versions = code_finite_nat_default (finite_asset_versions ddl_financial),
      rust_lock_clock = finite_clock ddl_financial, rust_lock_epoch = ddl_epoch,
      rust_lock_footprint = set ddl_footprint,
      rust_lock_grants = (if ddl_granted then {(Normal_Lock_Entry,ddl_actor)} else {}),
      rust_lock_balance = ddl_balance, rust_lock_funding = ddl_funding\<rparr>"

lemma ddl_opening_rust_image_uses_the_same_selected_financial_projection:
  assumes "ddl_funding \<le> ddl_balance"
    and "code_finite_nat_default (finite_source_units ddl_financial) (source_account_of ddl_binding_value) =
      ddl_balance - ddl_funding"
  shows "rust_lock_image_matches ddl_binding_value 0
    (ddl_rust_image ddl_financial ddl_footprint ddl_epoch ddl_actor ddl_granted ddl_balance ddl_funding)
    (code_interpret_finite_financial ddl_financial)"
  using assms by (simp add: rust_lock_image_matches_def ddl_rust_image_def code_interpret_finite_financial_def)

lemma ddl_equal_deadline_cannot_hold_the_finite_current_claim:
  assumes "map_of (finite_reservations ddl_financial) (binding_key (request_binding ddl_request_value)) = Some ddl_stored"
    and "finite_clock ddl_financial = reservation_deadline ddl_stored"
  shows "\<not> code_finite_closed_owns ddl_context ddl_request_value ddl_generation ddl_versions ddl_financial"
  using assms by (simp add: code_finite_closed_owns_def)

lemma ddl_equal_deadline_refuses_the_closed_dispatch:
  assumes "map_of (finite_reservations (finite_machine_state ddl_machine))
      (binding_key (request_binding ddl_request_value)) = Some ddl_stored"
    and "finite_clock (finite_machine_state ddl_machine) = reservation_deadline ddl_stored"
  shows "snd (code_finite_closed_dispatch ddl_context ddl_request_value ddl_generation ddl_versions ddl_machine) = Request_Rejected"
proof -
  have "\<not> code_finite_closed_owns ddl_context ddl_request_value ddl_generation ddl_versions (finite_machine_state ddl_machine)"
    by (rule ddl_equal_deadline_cannot_hold_the_finite_current_claim[OF assms])
  then show ?thesis
    by (simp add: code_finite_closed_dispatch_def code_finite_record_observation_def Let_def)
qed

lemma ddl_equal_deadline_refuses_the_rust_debit_projection:
  assumes "rust_lock_slots ddl_image (binding_key ddl_binding_value) = Some ddl_slot"
    and "rust_lock_clock ddl_image = rust_slot_expires ddl_slot"
  shows "rust_submit_debit ddl_registered ddl_verified Normal_Lock_Entry ddl_actor ddl_credential_value
    ddl_binding_value ddl_generation ddl_versions ddl_image = (ddl_image,Request_Rejected)"
  using assms by (simp add: rust_submit_debit_def Let_def)

fun ddl_reply_word where
  "ddl_reply_word Request_Rejected = (0::integer)"
| "ddl_reply_word Source_Dispatched = 1"
| "ddl_reply_word Source_Debited = 2"
| "ddl_reply_word _ = 3"

definition ddl_bit :: "bool \<Rightarrow> integer" where
  "ddl_bit ddl_predicate = (if ddl_predicate then 1 else 0)"

definition ddl_run_projection where
  "ddl_run_projection ddl_command ddl_is_debit ddl_descriptor ddl_machine ddl_request_value ddl_stored
      ddl_credential_value ddl_generation ddl_registered ddl_verified ddl_granted ddl_actor ddl_balance ddl_funding =
    (let ddl_financial = finite_machine_state ddl_machine; ddl_binding_value = request_binding ddl_request_value;
         ddl_key = binding_key ddl_binding_value; ddl_account = source_account_of ddl_binding_value;
         ddl_slot = rust_slot_of ddl_stored; ddl_versions = code_model_version_at [];
         ddl_code = ddl_rust_image ddl_financial (code_finite_closed_footprint ddl_descriptor ddl_binding_value)
           (finite_context_authority_epoch ddl_descriptor) ddl_actor ddl_granted ddl_balance ddl_funding;
         ddl_bound = rust_bound_debit ddl_registered ddl_verified Normal_Lock_Entry ddl_actor ddl_credential_value
           ddl_binding_value ddl_generation ddl_versions ddl_code ddl_slot;
         ddl_owns = code_finite_closed_owns ddl_descriptor ddl_request_value ddl_generation ddl_versions ddl_financial;
         (ddl_after,ddl_reply) = (if ddl_bound then code_finite_closed_command ddl_descriptor ddl_request_value [] ddl_command ddl_machine
           else (ddl_machine,Request_Rejected));
         ddl_state = finite_machine_state ddl_after;
         ddl_phase = map_option reservation_phase (map_of (finite_reservations ddl_state) ddl_key);
         ddl_finite_available = code_finite_nat_default (finite_source_units ddl_state) ddl_account;
         ddl_rust = (if ddl_is_debit then
           let (ddl_next,ddl_native_reply) = rust_submit_debit ddl_registered ddl_verified Normal_Lock_Entry ddl_actor ddl_credential_value
               ddl_binding_value ddl_generation ddl_versions ddl_code
           in [1,ddl_reply_word ddl_native_reply,
                code_finite_phase_integer (map_option rust_slot_phase (rust_lock_slots ddl_next ddl_key)),
                integer_of_nat (rust_lock_balance ddl_next)]
           else [0,0,0,0])
     in [integer_of_nat (finite_clock ddl_financial),integer_of_nat (reservation_deadline ddl_stored),
         ddl_bit (finite_clock ddl_financial < reservation_deadline ddl_stored),ddl_bit ddl_bound,ddl_bit ddl_owns,
         ddl_reply_word ddl_reply,code_finite_phase_integer (Some (reservation_phase ddl_stored)),
         code_finite_phase_integer ddl_phase,integer_of_nat ddl_balance,
         integer_of_nat (ddl_finite_available + ddl_funding)] @ ddl_rust)"

definition ddl_opening where
  "ddl_opening ddl_runner ddl_requested_binding ddl_stored_binding ddl_token ddl_before ddl_header =
    (let ddl_descriptor = integer_runner_context ddl_runner; ddl_slice = integer_runner_slice ddl_runner;
         ddl_base = slice_financial ddl_slice; ddl_base_state = finite_machine_state ddl_base;
         ddl_epoch = finite_context_authority_epoch ddl_descriptor; ddl_separator = slice_separator ddl_slice
     in case (ddl_binding ddl_epoch ddl_separator ddl_requested_binding,
              ddl_binding ddl_epoch ddl_separator ddl_stored_binding,ddl_credential ddl_token,ddl_before,ddl_header) of
       (Some ddl_request_binding,Some ddl_slot_binding,Some ddl_credential_value,
        [ddl_clock,ddl_expiry,ddl_phase,ddl_holder,ddl_slot_generation,ddl_active_asset,ddl_active_source,ddl_active_event,
         ddl_asset_value,ddl_asset_version,ddl_funding],
        [ddl_op,ddl_actor,ddl_caller,ddl_cut_epoch,ddl_generation,ddl_registered,ddl_granted,ddl_verified]) \<Rightarrow>
         let ddl_asset = binding_asset ddl_request_binding; ddl_account = source_account_of ddl_request_binding;
             ddl_balance = code_finite_nat_default (finite_source_units ddl_base_state) ddl_account;
             ddl_requested = ddl_request ddl_request_binding ddl_caller ddl_cut_epoch (finite_context_version ddl_descriptor);
             ddl_stored = \<lparr>reservation_binding = ddl_slot_binding, reservation_footprint = [ddl_active_asset],
               reservation_worker = ddl_holder,
               reservation_generation = ddl_slot_generation, reservation_deadline = ddl_expiry,
               reservation_phase = (if ddl_phase = 1 then Reservation_Held else Source_Submitted)\<rparr>;
             ddl_financial = ddl_base_state\<lparr>
               finite_asset_owners := [(ddl_active_asset,(ddl_active_source,ddl_active_event))],
               finite_reservations := [(binding_key ddl_slot_binding,ddl_stored)],
               finite_asset_values := [(ddl_asset,ddl_asset_value)], finite_asset_versions := [(ddl_asset,ddl_asset_version)],
               finite_source_units := [(ddl_account,ddl_balance - ddl_funding)], finite_clock := ddl_clock\<rparr>;
             ddl_command = (if ddl_op = 1 then Code_Finite_Dispatch ddl_generation else Code_Finite_Debit ddl_generation)
         in if ddl_op \<notin> {1,2} \<or> ddl_phase \<notin> {1,2} \<or> ddl_registered > 1 \<or> ddl_granted > 1 \<or> ddl_verified > 1 \<or>
               ddl_funding > ddl_balance \<or> ddl_requested_binding \<noteq> ddl_stored_binding \<or>
               ddl_account \<noteq> integer_runner_source ddl_runner \<or> ddl_caller \<noteq> ddl_actor
            then None
            else Some (ddl_run_projection ddl_command (ddl_op = 2) ddl_descriptor
              (ddl_base\<lparr>finite_machine_state := ddl_financial\<rparr>) ddl_requested ddl_stored ddl_credential_value ddl_generation
              (ddl_registered = 1) (ddl_verified = 1) (ddl_granted = 1) ddl_actor ddl_balance ddl_funding)
       | _ \<Rightarrow> None)"

definition ddl_submit_integer :: "integer list list \<Rightarrow> integer list option" where
  "ddl_submit_integer ddl_inputs =
    (if \<not> code_integer_u64_values (concat ddl_inputs) then None
     else case ddl_inputs of [ddl_metadata,ddl_request_binding,ddl_stored_binding,ddl_token,ddl_before,ddl_header] \<Rightarrow>
       (case ddl_header of [ddl_op,ddl_actor,ddl_caller,ddl_cut_epoch,ddl_generation,ddl_registered,ddl_granted,ddl_verified] \<Rightarrow>
         Option.bind (code_finite_single_asset_seed ddl_metadata (if ddl_granted = 1 then [ddl_actor] else []))
           (\<lambda>ddl_runner. ddl_opening ddl_runner (map nat_of_integer ddl_request_binding)
              (map nat_of_integer ddl_stored_binding) (map nat_of_integer ddl_token) (map nat_of_integer ddl_before)
              (map nat_of_integer ddl_header))
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      ddl_opening_rust_image_uses_the_same_selected_financial_projection
      ddl_equal_deadline_cannot_hold_the_finite_current_claim
      ddl_equal_deadline_refuses_the_closed_dispatch
      ddl_equal_deadline_refuses_the_rust_debit_projection
      closed_ownership_is_exactly_the_interpreted_existing_finite_query
      each_closed_data_command_is_exactly_its_frozen_financial_operation
      the_native_debit_lease_checks_match_the_model_authority
      rust_debit_consumes_the_related_current_lease_and_matches_state_and_reply})
  then () else error "Unexpected oracle in Dispatch/Debit lease link"
\<close>

export_code ddl_submit_integer in SML module_name OIP_Dispatch_Debit_Lease_ABI file_prefix "oip_dispatch_debit_lease_abi"

end
