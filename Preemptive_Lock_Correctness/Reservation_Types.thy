(* SPDX-License-Identifier: BSD-3-Clause *)
theory Reservation_Types
  imports "Cross_Chain_Message_Integrity.Message_Consumers"
    "Cross_Domain_State_Preservation.Composition"
    "Cross_Domain_State_Preservation.Functor_Laws"
begin

section \<open>Reservations, Workers and Financial Effects\<close>

datatype reservation_phase =
    Reservation_Held | Source_Submitted | Source_Pending
  | Source_Confirmed | Source_Returned | Source_Cancelled

record asset_reservation =
  reservation_binding :: transfer_binding
  reservation_footprint :: "nat list"
  reservation_worker :: nat
  reservation_generation :: nat
  reservation_deadline :: nat
  reservation_phase :: reservation_phase

record lock_context =
  lock_authority :: execution_context
  lock_metadata :: global_state
  lock_restrictions :: "nat \<Rightarrow> bool"
  lock_dependencies :: "nat \<Rightarrow> nat list"
  lock_write_permissions :: "(nat \<times> nat \<times> nat) set"
  lock_spend_permissions :: "(nat \<times> source_key \<times> nat \<times> nat \<times> nat \<times> message_operation) set"

definition required_footprint :: "lock_context \<Rightarrow> transfer_binding \<Rightarrow> nat list" where
  "required_footprint c b = remdups(binding_asset b # lock_dependencies c (binding_asset b))"

type_synonym source_account = "nat \<times> nat"
type_synonym destination_account = "nat \<times> nat \<times> nat"

definition source_account_of :: "transfer_binding \<Rightarrow> source_account" where
  "source_account_of b = (fst(binding_key b),binding_asset b)"

definition destination_account_of :: "transfer_binding \<Rightarrow> destination_account" where
  "destination_account_of b = (binding_destination b,binding_asset b,binding_recipient b)"

definition holder_account :: "transfer_binding \<Rightarrow> nat \<Rightarrow> destination_account" where
  "holder_account b holder = (binding_destination b,binding_asset b,holder)"

record descendant_effect =
  lineage_root :: transfer_binding
  lineage_from :: nat
  lineage_to :: nat
  lineage_amount :: nat
  lineage_operation :: message_operation
  lineage_caller :: nat
  lineage_authority_epoch :: nat
  lineage_version :: nat

record reservation_state =
  asset_owner :: "nat \<Rightarrow> source_key option"
  reservation_at :: "source_key \<Rightarrow> asset_reservation option"
  asset_value :: "nat \<Rightarrow> nat"
  asset_version :: "nat \<Rightarrow> nat"
  source_units :: "source_account \<Rightarrow> nat"
  destination_units :: "destination_account \<Rightarrow> nat"
  funded_units :: "(source_key \<times> destination_account) \<Rightarrow> nat"
  source_effects :: "transfer_binding list"
  issued_certificates :: "source_certificate list"
  received_messages :: message_state
  lawful_descendants :: "descendant_effect list"
  reservation_clock :: nat

datatype reservation_reply =
    Request_Rejected | Reservation_Busy | Reservation_Acquired
  | Source_Dispatched | Source_Debited | Source_Already_Debited
  | Source_Fenced
  | Worker_Reassigned | Data_Updated
  | Reservation_Released | Descendant_Executed
  | Delivery_Response message_reply
  | Value_Response nat

record completed_observation =
  observation_key :: source_key
  observation_binding :: transfer_binding
  observation_asset :: nat
  observation_caller :: nat
  observation_version :: nat
  observation_authority_epoch :: nat
  observation_reply :: reservation_reply

datatype reservation_event =
    Acquired_Event asset_reservation
  | Dispatched_Event source_key
  | Source_Effect_Event transfer_binding
  | Worker_Event source_key nat nat nat
  | Data_Event nat nat nat
  | Certificate_Event source_certificate
  | Credit_Event transfer_binding
  | Cancel_Event source_key
  | Source_Fence_Event source_key
  | Return_Event transfer_binding
  | Confirm_Event source_key
  | Descendant_Event descendant_effect
  | Clock_Event nat

record reservation_machine =
  machine_state :: reservation_state
  machine_journal :: "reservation_event list"
  machine_observations :: "completed_observation list"

definition initial_reservation_state :: "(source_account \<Rightarrow> nat) \<Rightarrow> reservation_state"
  where
  "initial_reservation_state balances =
    \<lparr>asset_owner=(\<lambda>_.None),reservation_at=(\<lambda>_.None),
      asset_value=(\<lambda>_.0),asset_version=(\<lambda>_.0),source_units=balances,
      destination_units=(\<lambda>_.0),funded_units=(\<lambda>_.0),source_effects=[],issued_certificates=[],
      received_messages=empty_message_state,lawful_descendants=[],reservation_clock=0\<rparr>"

definition initial_reservation_machine :: "(source_account \<Rightarrow> nat) \<Rightarrow> reservation_machine"
  where
  "initial_reservation_machine balances =
    \<lparr>machine_state=initial_reservation_state balances,machine_journal=[],machine_observations=[]\<rparr>"

fun active_reservation_phase :: "reservation_phase \<Rightarrow> bool" where
  "active_reservation_phase Reservation_Held=True"
| "active_reservation_phase Source_Submitted=True"
| "active_reservation_phase Source_Pending=True"
| "active_reservation_phase _=False"

definition source_was_debited :: "reservation_state \<Rightarrow> source_key \<Rightarrow> bool" where
  "source_was_debited s key \<longleftrightarrow> key\<in>set(map binding_key(source_effects s))"

definition binding_is_registered :: "reservation_state \<Rightarrow> transfer_binding \<Rightarrow> bool" where
  "binding_is_registered s b \<longleftrightarrow>
    (\<exists>res. reservation_at s (binding_key b)=Some res \<and> reservation_binding res=b)"

definition owns_recorded_reservation :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_state \<Rightarrow> bool" where
  "owns_recorded_reservation c r generation versions s \<longleftrightarrow>
    current_use_allowed(lock_authority c) r \<and>
    (\<exists>res. reservation_at s (binding_key(request_binding r))=Some res \<and>
      reservation_binding res=request_binding r \<and>
      reservation_worker res=request_caller r \<and>
      reservation_generation res=generation \<and>
      reservation_clock s < reservation_deadline res \<and>
      active_reservation_phase(reservation_phase res) \<and>
      (\<forall>a\<in>set(reservation_footprint res).
        asset_owner s a=Some(binding_key(request_binding r)) \<and> versions a=asset_version s a))"

definition owns_current_reservation :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> reservation_state \<Rightarrow> bool" where
  "owns_current_reservation c r generation versions s \<longleftrightarrow>
    owns_recorded_reservation c r generation versions s \<and>
    (\<forall>res. reservation_at s(binding_key(request_binding r))=Some res \<longrightarrow>
      set(reservation_footprint res)=set(required_footprint c(request_binding r)))"

definition phase_at :: "reservation_state \<Rightarrow> source_key \<Rightarrow> reservation_phase option"
  where
  "phase_at s key = map_option reservation_phase (reservation_at s key)"

definition set_phase :: "source_key \<Rightarrow> reservation_phase \<Rightarrow> reservation_state
  \<Rightarrow> reservation_state" where
  "set_phase key phase s = s\<lparr>reservation_at := (reservation_at s)
    (key := map_option (\<lambda>res. res\<lparr>reservation_phase:=phase\<rparr>) (reservation_at s key))\<rparr>"

definition finish_reservation :: "source_key \<Rightarrow> reservation_phase \<Rightarrow> reservation_state
  \<Rightarrow> reservation_state" where
  "finish_reservation key phase s =
    (set_phase key phase s)\<lparr>asset_owner :=
      (\<lambda>a. if asset_owner s a=Some key then None else asset_owner s a)\<rparr>"

fun apply_reservation_event :: "reservation_event \<Rightarrow> reservation_state \<Rightarrow> reservation_state"
  where
  "apply_reservation_event (Acquired_Event res) s =
    s\<lparr>reservation_at := (reservation_at s)(binding_key(reservation_binding res):=Some res),
      asset_owner := (\<lambda>a. if a\<in>set(reservation_footprint res)
        then Some(binding_key(reservation_binding res)) else asset_owner s a)\<rparr>"
| "apply_reservation_event (Dispatched_Event key) s = set_phase key Source_Submitted s"
| "apply_reservation_event (Source_Effect_Event b) s =
    (set_phase (binding_key b) Source_Pending s)\<lparr>
      source_units := (source_units s)(source_account_of b := source_units s (source_account_of b)-binding_amount b),
      source_effects := source_effects s@[b]\<rparr>"
| "apply_reservation_event (Worker_Event key worker generation deadline) s =
    s\<lparr>reservation_at := (reservation_at s)(key := map_option (\<lambda>res.
      res\<lparr>reservation_worker:=worker,reservation_generation:=generation,reservation_deadline:=deadline\<rparr>)
      (reservation_at s key))\<rparr>"
| "apply_reservation_event (Data_Event asset value version) s =
    s\<lparr>asset_value:=(asset_value s)(asset:=value),asset_version:=(asset_version s)(asset:=version)\<rparr>"
| "apply_reservation_event (Certificate_Event cert) s =
    s\<lparr>issued_certificates:=issued_certificates s@[cert]\<rparr>"
| "apply_reservation_event (Credit_Event b) s =
    s\<lparr>received_messages:=record_credit b (received_messages s),
      destination_units:=(destination_units s)
        (destination_account_of b:=destination_units s(destination_account_of b)+binding_amount b),
      funded_units:=(funded_units s)((binding_key b,destination_account_of b):=
        funded_units s(binding_key b,destination_account_of b)+binding_amount b)\<rparr>"
| "apply_reservation_event (Cancel_Event key) s = finish_reservation key Source_Cancelled s"
| "apply_reservation_event (Source_Fence_Event key) s = finish_reservation key Source_Cancelled s"
| "apply_reservation_event (Return_Event b) s =
    (finish_reservation (binding_key b) Source_Returned s)\<lparr>source_units:=(source_units s)
      (source_account_of b:=source_units s(source_account_of b)+binding_amount b)\<rparr>"
| "apply_reservation_event (Confirm_Event key) s = finish_reservation key Source_Confirmed s"
| "apply_reservation_event (Descendant_Event effect) s =
    (let b=lineage_root effect; amount=lineage_amount effect;
       source=holder_account b(lineage_from effect); target=holder_account b(lineage_to effect);
       units=(destination_units s)(source:=destination_units s source-amount);
       lots=(funded_units s)((binding_key b,source):=funded_units s(binding_key b,source)-amount)
     in s\<lparr>destination_units:=units(target:=units target+amount),
       funded_units:=lots((binding_key b,target):=lots(binding_key b,target)+amount),
       lawful_descendants:=lawful_descendants s@[effect]\<rparr>)"
| "apply_reservation_event (Clock_Event time) s = s\<lparr>reservation_clock:=time\<rparr>"

definition commit_reservation_event :: "reservation_event \<Rightarrow> reservation_machine \<Rightarrow>
  reservation_machine" where
  "commit_reservation_event e m = m\<lparr>machine_state:=apply_reservation_event e (machine_state m),
    machine_journal:=machine_journal m@[e]\<rparr>"

definition record_observation :: "execution_request \<Rightarrow> reservation_reply \<Rightarrow>
  reservation_machine \<Rightarrow> reservation_machine \<times> reservation_reply" where
  "record_observation r reply m =
    (m\<lparr>machine_observations:=machine_observations m@[
       \<lparr>observation_key=binding_key(request_binding r),observation_binding=request_binding r,
         observation_asset=binding_asset(request_binding r),observation_caller=request_caller r,
         observation_version=request_version r,observation_authority_epoch=request_authority_epoch r,
         observation_reply=reply\<rparr>]\<rparr>,reply)"

definition replay_reservation_events :: "(source_account \<Rightarrow> nat) \<Rightarrow>
  reservation_event list \<Rightarrow> reservation_state" where
  "replay_reservation_events balances events = fold apply_reservation_event events (initial_reservation_state balances)"

text \<open>The source account is an allocation pool identified by source domain
  and asset. An adapter must relate that pool to actual source holdings.
  Completed observations are a proof history; they are distinct from the
  financial journal. Asset values are committed application data, not tentative
  values of an abortable binding transaction. Root-indexed funding records
  distinguish financial lineage even when account balances are pooled.
  A durable implementation must realize each committed
  effect and its journal record together.\<close>

end
