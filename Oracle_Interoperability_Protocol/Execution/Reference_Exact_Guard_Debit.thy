theory Reference_Exact_Guard_Debit
  imports "OIP_Reference_Profile.Reference_Exact_Guard_Packets" Reference_Lock_Code
begin

definition guard_debit_lease :: rust_lock_image where
  "guard_debit_lease = \<lparr>rust_lock_slots = (\<lambda>_. None)((0,17) := Some
       \<lparr>rust_slot_binding = \<lparr>binding_key = (0,17), binding_asset = 17, binding_amount = 5, binding_destination = 2,
          binding_recipient = 3, binding_source_epoch = 9, binding_operation = Destination_Credit, binding_separator = 0\<rparr>,
          rust_slot_holder = 7, rust_slot_generation = 0, rust_slot_expires = 20,
          rust_slot_phase = Source_Submitted, rust_slot_footprint = {17}\<rparr>),
      rust_lock_active = (\<lambda>_. None)(17 := Some (0,17)), rust_lock_versions = (\<lambda>_. 0),
      rust_lock_clock = 0, rust_lock_epoch = 9, rust_lock_footprint = {17},
      rust_lock_grants = {(Normal_Lock_Entry,7),(Normal_Lock_Entry,8)}, rust_lock_balance = 10, rust_lock_funding = 0\<rparr>"

definition guard_debit_without_command_generation where
  "guard_debit_without_command_generation registered verified entry actor credential binding generation versions code =
     (let slot = rust_lock_slots code (binding_key binding);
          current = (case slot of None \<Rightarrow> generation | Some value \<Rightarrow> rust_slot_generation value)
      in rust_submit_debit registered verified entry actor credential binding current versions code)"

definition run_exact_guard_debit where
  "run_exact_guard_debit submit bytes state =
    (case decode_wire_packet bytes of None \<Rightarrow> None | Some packet \<Rightarrow>
       let core = packet_core packet in
       case decode_native_call_prefix core of None \<Rightarrow> None | Some native \<Rightarrow>
         case decode_ordinary_operands core native of Some (Some credential, versions, Wire_Debit generation) \<Rightarrow>
           Some (submit True True Normal_Lock_Entry (fst (native_id native)) credential
             \<lparr>binding_key = native_origin native, binding_asset = native_asset native, binding_amount = native_amount native,
               binding_destination = native_destination native, binding_recipient = native_recipient native,
               binding_source_epoch = native_origin_epoch native, binding_operation = Destination_Credit, binding_separator = 0\<rparr>
             generation (\<lambda>asset. case map_of versions asset of None \<Rightarrow> 0 | Some version \<Rightarrow> version) state)
         | _ \<Rightarrow> None)"

lemma the_same_signed_debit_bytes_are_refused_and_spend_if_generation_is_ignored:
  "run_exact_guard_debit rust_submit_debit guard_debit_packet_bytes guard_debit_lease = Some (guard_debit_lease,Request_Rejected)"
  "map_option (\<lambda>(after,reply). (map_option rust_slot_phase (rust_lock_slots after (0,17)), rust_lock_balance after, reply))
       (run_exact_guard_debit guard_debit_without_command_generation guard_debit_packet_bytes guard_debit_lease) =
       Some (Some Source_Pending,5,Source_Debited)"
  by (simp_all add: run_exact_guard_debit_def guard_debit_decodes_from_the_full_native_envelope
     guard_debit_core_def guard_debit_body_def decode_native_call_prefix_def decode_ordinary_operands_def
     decode_wire_credential_prefix_def decode_ordinary_tail_def wire_octets_def
     guard_debit_without_command_generation_def rust_submit_debit_def rust_bound_debit_def guard_debit_lease_def Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_same_signed_debit_bytes_are_refused_and_spend_if_generation_is_ignored})
  then () else error "Unexpected oracle in exact debit guard comparison"
\<close>

end
