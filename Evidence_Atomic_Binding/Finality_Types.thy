(* SPDX-License-Identifier: BSD-3-Clause *)
theory Finality_Types
  imports Root_Funding_Bounds
begin

section \<open>Terminal Records and Protocol Intents\<close>

datatype terminal_kind = Confirmed_Decision | Reversed_Decision

record terminal_record =
  terminal_binding :: transfer_binding
  terminal_kind :: terminal_kind
  terminal_evidence :: "source_certificate list"

type_synonym version_vector = "(nat \<times> nat) list"

definition vector_lookup :: "version_vector \<Rightarrow> nat \<Rightarrow> nat" where
  "vector_lookup versions asset=(case map_of versions asset of None \<Rightarrow> 0 | Some v \<Rightarrow> v)"

datatype protocol_intent =
    Reserve_Intent execution_request version_vector nat
  | Dispatch_Intent execution_request nat version_vector
  | Source_Intent execution_request nat version_vector
  | Cancel_Intent execution_request nat version_vector
  | Fence_Intent execution_request nat version_vector
  | Reassign_Intent execution_request nat
  | Write_Intent execution_request nat version_vector nat
  | Time_Intent nat
  | Certificate_Intent source_certificate
  | Deliver_Intent message_route execution_request
  | Return_Intent execution_request nat version_vector
  | Reconcile_Intent execution_request nat version_vector
  | Descendant_Intent execution_request transfer_binding nat nat nat
  | Data_Read_Intent execution_request

fun intent_request :: "protocol_intent \<Rightarrow> execution_request option" where
  "intent_request(Reserve_Intent r versions duration)=Some r"
| "intent_request(Dispatch_Intent r g versions)=Some r"
| "intent_request(Source_Intent r g versions)=Some r"
| "intent_request(Cancel_Intent r g versions)=Some r"
| "intent_request(Fence_Intent r g versions)=Some r"
| "intent_request(Reassign_Intent r duration)=Some r"
| "intent_request(Write_Intent r g versions value)=Some r"
| "intent_request(Deliver_Intent route r)=Some r"
| "intent_request(Return_Intent r g versions)=Some r"
| "intent_request(Reconcile_Intent r g versions)=Some r"
| "intent_request(Descendant_Intent r root sender recipient amount)=Some r"
| "intent_request(Data_Read_Intent r)=Some r"
| "intent_request _=None"

fun parent_action :: "lock_context \<Rightarrow> protocol_intent \<Rightarrow> reservation_action" where
  "parent_action c(Reserve_Intent r versions duration)=Acquire_Action c r(vector_lookup versions)duration"
| "parent_action c(Dispatch_Intent r g versions)=Dispatch_Action c r g(vector_lookup versions)"
| "parent_action c(Source_Intent r g versions)=Source_Action c r g(vector_lookup versions)"
| "parent_action c(Cancel_Intent r g versions)=Cancel_Action c r g(vector_lookup versions)"
| "parent_action c(Fence_Intent r g versions)=Fence_Action c r g(vector_lookup versions)"
| "parent_action c(Reassign_Intent r duration)=Reassign_Action c r duration"
| "parent_action c(Write_Intent r g versions value)=Write_Action c r g(vector_lookup versions)value"
| "parent_action c(Time_Intent elapsed)=Time_Action elapsed"
| "parent_action c(Certificate_Intent cert)=Publish_Action cert"
| "parent_action c(Deliver_Intent route r)=Deliver_Action route(lock_authority c)r"
| "parent_action c(Return_Intent r g versions)=Return_Action c r g(vector_lookup versions)"
| "parent_action c(Reconcile_Intent r g versions)=Reconcile_Action c r g(vector_lookup versions)"
| "parent_action c(Descendant_Intent r root sender recipient amount)=Descendant_Action c r root sender recipient amount"
| "parent_action c(Data_Read_Intent r)=Read_Action c r"

datatype finality_reply =
    Finality_Rejected
  | Terminal_Recorded
  | Evidence_Refreshed
  | Primary_Published
  | Context_Installed
  | Regulatory_Applied
  | Protocol_Response reservation_reply
  | Internal_Completed

record finality_core =
  core_parent :: reservation_machine
  core_records :: "source_key \<Rightarrow> terminal_record option"
  core_published :: "source_key set"
  core_regulatory :: regulatory_receiver
  core_contexts :: "nat \<Rightarrow> lock_context"
  core_epoch :: nat

definition initial_finality_core :: "(source_account \<Rightarrow> nat) \<Rightarrow> global_state
  \<Rightarrow> (nat \<Rightarrow> lock_context) \<Rightarrow> finality_core" where
  "initial_finality_core balances regulatory contexts=
    \<lparr>core_parent=initial_reservation_machine balances,core_records=(\<lambda>_.None),core_published={},
      core_regulatory=\<lparr>receiver_snapshot=regulatory,receiver_applied={}\<rparr>,
      core_contexts=contexts,core_epoch=0\<rparr>"

definition current_lock_view :: "finality_core \<Rightarrow> nat \<Rightarrow> lock_context" where
  "current_lock_view s endpoint=(core_contexts s endpoint)\<lparr>
    lock_metadata:=receiver_snapshot(core_regulatory s)\<rparr>"

fun kind_from_source :: "source_status \<Rightarrow> terminal_kind option" where
  "kind_from_source Finalized=Some Confirmed_Decision"
| "kind_from_source Reversed=Some Reversed_Decision"
| "kind_from_source Observed=None"

definition record_reference :: "finality_core \<Rightarrow> nat \<Rightarrow> transfer_binding
  \<Rightarrow> terminal_kind \<Rightarrow> source_certificate option" where
  "record_reference s index b kind=
    (case core_records s(binding_key b) of None \<Rightarrow> None
     | Some record \<Rightarrow>
       if terminal_binding record=b \<and> terminal_kind record=kind \<and>
          index<length(terminal_evidence record)
       then Some(terminal_evidence record!index) else None)"

definition exact_record_reference :: "finality_core \<Rightarrow> nat \<Rightarrow> transfer_binding
  \<Rightarrow> terminal_kind \<Rightarrow> source_certificate \<Rightarrow> bool" where
  "exact_record_reference s index b kind cert \<longleftrightarrow> record_reference s index b kind=Some cert"

datatype finality_operation =
    Record_Terminal source_certificate
  | Invoke_Protocol nat nat nat protocol_intent
  | Invoke_Regulatory nat nat nat execution_request
  | Publish_Primary source_key
  | Install_Context nat lock_context

text \<open>A protocol intent contains a request and a finite expected-version
  vector. Its authorization and regulatory context is read from the authority's
  current state, rather than supplied as a client assertion. The epoch in
  Invoke Protocol identifies that current state and is checked at execution.
  Install Context represents an authenticated input from the existing policy
  and authority provider. Authenticity of that external provider is an explicit
  implementation obligation, not a conclusion of this model.\<close>

end
