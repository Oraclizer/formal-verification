(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Protocol
  imports Reservation_Types
begin

section \<open>Source Control and Independent Destination Delivery\<close>

definition metadata_permission :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> bool" where
  "metadata_permission c r domain =
    (case get_reg_state(lock_metadata c) domain (binding_asset(request_binding r)) of
       None \<Rightarrow> False
     | Some state \<Rightarrow>
       (case binding_operation(request_binding r) of
          Destination_Credit \<Rightarrow> ordinary_transfer_allowed
            (current_use_allowed(lock_authority c) r) (lock_restrictions c (binding_asset(request_binding r))) state
        | Ordinary_Transfer_Effect \<Rightarrow> ordinary_transfer_allowed
            (current_use_allowed(lock_authority c) r) (lock_restrictions c (binding_asset(request_binding r))) state
        | Enforcement_Transfer_Effect kind \<Rightarrow> transfer_allowed state
            \<lparr>transfer_path_value=Authorized_Enforcement kind,baseline_clear=False,
              restriction_clear=lock_restrictions c (binding_asset(request_binding r)),
              enforcement_approved=current_use_allowed(lock_authority c) r\<rparr>
        | _ \<Rightarrow> False))"

definition acquire_reservation :: "lock_context \<Rightarrow> execution_request \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "acquire_reservation c r versions duration m =
    (let s=machine_state m; b=request_binding r; footprint=required_footprint c b
     in if \<not>current_use_allowed(lock_authority c) r \<or> duration=0 \<or>
           reservation_at s (binding_key b)\<noteq>None \<or>
           (\<exists>a\<in>set footprint. versions a\<noteq>asset_version s a)
        then record_observation r Request_Rejected m
        else if (\<exists>a\<in>set footprint. asset_owner s a\<noteq>None)
        then record_observation r Reservation_Busy m
        else record_observation r Reservation_Acquired
          (commit_reservation_event (Acquired_Event
             \<lparr>reservation_binding=b,reservation_footprint=footprint,
               reservation_worker=request_caller r,reservation_generation=0,
               reservation_deadline=reservation_clock s+duration,reservation_phase=Reservation_Held\<rparr>) m))"

definition dispatch_source :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "dispatch_source c r g versions m =
    (if owns_current_reservation c r g versions (machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Reservation_Held \<and>
        binding_operation(request_binding r)=Destination_Credit \<and>
        0<binding_amount(request_binding r) \<and>
        binding_amount(request_binding r)\<le>source_units(machine_state m)(source_account_of(request_binding r)) \<and>
        metadata_permission c r(fst(binding_key(request_binding r)))
     then record_observation r Source_Dispatched
       (commit_reservation_event(Dispatched_Event(binding_key(request_binding r)))m)
     else record_observation r Request_Rejected m)"

definition execute_source_effect :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "execute_source_effect c r g versions m =
    (let s=machine_state m; b=request_binding r in
     if \<not>current_use_allowed(lock_authority c) r \<or> \<not>binding_is_registered s b
     then record_observation r Request_Rejected m
     else if source_was_debited s (binding_key b)
     then record_observation r Source_Already_Debited m
     else if owns_current_reservation c r g versions s \<and>
          phase_at s (binding_key b)\<in>{Some Source_Submitted,Some Source_Pending} \<and>
          binding_operation b=Destination_Credit \<and> 0<binding_amount b \<and>
          binding_amount b\<le>source_units s(source_account_of b) \<and>
          context_endpoint(lock_authority c)=fst(binding_key b) \<and>
          metadata_permission c r (fst(binding_key b))
     then record_observation r Source_Debited(commit_reservation_event(Source_Effect_Event b)m)
     else record_observation r Request_Rejected m)"

definition cancel_before_dispatch :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "cancel_before_dispatch c r g versions m =
    (if owns_recorded_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Reservation_Held
     then record_observation r Reservation_Released
       (commit_reservation_event(Cancel_Event(binding_key(request_binding r)))m)
     else record_observation r Request_Rejected m)"

definition fence_unexecuted_source :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "fence_unexecuted_source c r g versions m =
    (if owns_recorded_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))\<in>{Some Source_Submitted,Some Source_Pending} \<and>
        \<not>source_was_debited(machine_state m)(binding_key(request_binding r)) \<and>
        context_endpoint(lock_authority c)=fst(binding_key(request_binding r))
     then record_observation r Source_Fenced
       (commit_reservation_event(Source_Fence_Event(binding_key(request_binding r)))m)
     else record_observation r Request_Rejected m)"

definition reassign_worker :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> reservation_machine \<Rightarrow> reservation_machine \<times> reservation_reply" where
  "reassign_worker c r duration m =
    (case reservation_at(machine_state m)(binding_key(request_binding r)) of
       None \<Rightarrow> record_observation r Request_Rejected m
     | Some res \<Rightarrow>
       if current_use_allowed(lock_authority c) r \<and> duration>0 \<and>
          reservation_binding res=request_binding r \<and> active_reservation_phase(reservation_phase res) \<and>
          reservation_deadline res\<le>reservation_clock(machine_state m)
       then record_observation r Worker_Reassigned(commit_reservation_event
         (Worker_Event(binding_key(request_binding r))(request_caller r)
           (Suc(reservation_generation res))(reservation_clock(machine_state m)+duration))m)
       else record_observation r Request_Rejected m)"

definition write_asset_data :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "write_asset_data c r g versions value m =
    (if owns_current_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Reservation_Held \<and>
        (request_caller r,binding_asset(request_binding r),value)\<in>lock_write_permissions c
     then record_observation r Data_Updated(commit_reservation_event
       (Data_Event(binding_asset(request_binding r))value
         (Suc(asset_version(machine_state m)(binding_asset(request_binding r)))))m)
     else record_observation r Request_Rejected m)"

definition advance_reservation_time :: "nat \<Rightarrow> reservation_machine \<Rightarrow> reservation_machine"
  where
  "advance_reservation_time elapsed m = commit_reservation_event
    (Clock_Event(reservation_clock(machine_state m)+elapsed))m"

context source_attestation
begin

lemma published_verifier_interpretation:
  "source_attestation roster faulty fault_bound threshold
    (\<lambda>cert. verifies cert \<and> cert\<in>set published) signed source_truth stable_source"
  using source_attestation_axioms unfolding source_attestation_def by blast

definition publish_source_certificate :: "source_certificate \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine" where
  "publish_source_certificate cert m =
    (let b=statement_binding(certificate_statement cert) in
     if certificate_ok cert \<and> statement_status(certificate_statement cert)\<noteq>Observed \<and>
        b\<in>set(source_effects(machine_state m))
     then commit_reservation_event(Certificate_Event cert)m else m)"

definition published_receive :: "message_route \<Rightarrow> execution_context \<Rightarrow> execution_request
  \<Rightarrow> reservation_state \<Rightarrow> message_state \<times> message_reply" where
  "published_receive route c r s = source_attestation.receive_credit roster threshold
    (\<lambda>cert. verifies cert \<and> cert\<in>set(issued_certificates s)) route c r (received_messages s)"

lemma published_receive_expansion:
  "published_receive route c r s =
    (if \<not>(credit_admissible c r \<and> request_certificate r\<in>set(issued_certificates s))
     then (received_messages s,Message_Rejected)
     else if credit_marker(request_binding r)\<in>consumed_at(received_messages s)
     then (received_messages s,Duplicate_Credit(request_binding r))
     else (record_credit(request_binding r)(received_messages s),New_Credit(request_binding r)))"
  unfolding published_receive_def
  by (simp add: source_attestation.receive_credit_def[OF published_verifier_interpretation]
      source_attestation.credit_admissible_def[OF published_verifier_interpretation]
      source_attestation.authenticated_request_def[OF published_verifier_interpretation]
      source_attestation.certificate_ok_def[OF published_verifier_interpretation]
      credit_admissible_def authenticated_request_def certificate_ok_def)

definition deliver_reserved_credit :: "message_route \<Rightarrow> execution_context \<Rightarrow>
  execution_request \<Rightarrow> reservation_machine \<Rightarrow> reservation_machine \<times> reservation_reply"
  where
  "deliver_reserved_credit route c r m =
    (case snd(published_receive route c r(machine_state m)) of
       New_Credit b \<Rightarrow> record_observation r (Delivery_Response(New_Credit b))
         (commit_reservation_event(Credit_Event b)m)
     | reply \<Rightarrow> record_observation r (Delivery_Response reply)m)"

definition reversed_source_evidence :: "execution_context \<Rightarrow> execution_request \<Rightarrow>
  reservation_state \<Rightarrow> bool" where
  "reversed_source_evidence c r s \<longleftrightarrow>
    request_certificate r\<in>set(issued_certificates s) \<and> certificate_ok(request_certificate r) \<and>
    certificate_epoch(request_certificate r)=context_relay_epoch c \<and>
    statement_binding(certificate_statement(request_certificate r))=request_binding r \<and>
    statement_status(certificate_statement(request_certificate r))=Reversed"

definition release_to_source :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "release_to_source c r g versions m =
    (if owns_recorded_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending \<and>
        reversed_source_evidence(lock_authority c)r(machine_state m)
     then record_observation r Reservation_Released(commit_reservation_event(Return_Event(request_binding r))m)
     else record_observation r Request_Rejected m)"

definition reconcile_recorded_credit :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "reconcile_recorded_credit c r g versions m =
    (if owns_recorded_reservation c r g versions(machine_state m) \<and>
        phase_at(machine_state m)(binding_key(request_binding r))=Some Source_Pending \<and>
        request_binding r\<in>set(credit_history(received_messages(machine_state m)))
     then record_observation r Reservation_Released
       (commit_reservation_event(Confirm_Event(binding_key(request_binding r)))m)
     else record_observation r Request_Rejected m)"

end

definition descendant_binding :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  message_operation \<Rightarrow> transfer_binding" where
  "descendant_binding root recipient amount operation =
    root\<lparr>binding_recipient:=recipient,binding_amount:=amount,binding_operation:=operation\<rparr>"

definition execute_descendant :: "lock_context \<Rightarrow> execution_request \<Rightarrow> transfer_binding
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine \<times> reservation_reply" where
  "execute_descendant c r root sender recipient amount m =
    (let operation=binding_operation(request_binding r) in
     if root\<in>set(credit_history(received_messages(machine_state m))) \<and>
        request_binding r=descendant_binding root recipient amount operation \<and>
        (operation=Ordinary_Transfer_Effect \<or> (\<exists>kind. operation=Enforcement_Transfer_Effect kind)) \<and>
        context_endpoint(lock_authority c)=binding_destination root \<and>
        metadata_permission c r (binding_destination root) \<and> 0<amount \<and>
        (request_caller r,binding_key root,sender,recipient,amount,operation)\<in>lock_spend_permissions c \<and>
        amount\<le>destination_units(machine_state m)(holder_account root sender) \<and>
        amount\<le>funded_units(machine_state m)(binding_key root,holder_account root sender)
     then record_observation r Descendant_Executed(commit_reservation_event(Descendant_Event
       \<lparr>lineage_root=root,lineage_from=sender,lineage_to=recipient,lineage_amount=amount,
         lineage_operation=operation,lineage_caller=request_caller r,
         lineage_authority_epoch=request_authority_epoch r,lineage_version=request_version r\<rparr>)m)
     else record_observation r Request_Rejected m)"

definition read_source_data :: "lock_context \<Rightarrow> execution_request \<Rightarrow> reservation_machine
  \<Rightarrow> reservation_machine \<times> reservation_reply" where
  "read_source_data c r m =
    (if \<not>current_read_allowed(lock_authority c)(request_caller r)(request_version r)
     then record_observation r Request_Rejected m
     else if asset_owner(machine_state m)(binding_asset(request_binding r))\<noteq>None
     then record_observation r Reservation_Busy m
     else record_observation r (Value_Response(asset_value(machine_state m)(binding_asset(request_binding r))))m)"

text \<open>Publication certifies a previously recorded source effect; it does
  not perform that effect again. A destination does not consult a source
  worker lease or wait for a local pending notification. Source reconciliation
  is a separate operation. The current regulatory view and authorization
  context must be supplied by their authoritative runtime providers.\<close>

text \<open>The non-effect fence executes at the authoritative source control
  endpoint. It checks the persistent source debit record and permanently closes
  the source key in one local step. An external effect outside that endpoint's
  control cannot use this guarantee without a separate source-side fence or
  non-effect proof. Terminal cleanup checks the footprint already held; it
  does not acquire a newly changed dependency footprint.\<close>

end
