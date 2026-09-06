(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Types
  imports "Regulatory_Action_Composition.Regulatory_Action_Composition"
begin

section \<open>Source Identity and Execution Context\<close>

type_synonym source_key = "nat \<times> nat"

datatype message_operation =
    Destination_Credit
  | Ordinary_Transfer_Effect
  | Enforcement_Transfer_Effect legal_action_kind
  | Regulatory_State_Effect reg_action

record transfer_binding =
  binding_key :: source_key
  binding_asset :: nat
  binding_amount :: nat
  binding_destination :: nat
  binding_recipient :: nat
  binding_source_epoch :: nat
  binding_operation :: message_operation
  binding_separator :: nat

datatype source_status = Observed | Finalized | Reversed

record source_statement =
  statement_binding :: transfer_binding
  statement_status :: source_status

record source_certificate =
  certificate_statement :: source_statement
  certificate_epoch :: nat
  certificate_signers :: "nat list"
  certificate_signature :: nat

record execution_context =
  context_endpoint :: nat
  context_relay_epoch :: nat
  context_authority_epoch :: nat
  context_version :: nat
  context_permissions :: "(nat \<times> transfer_binding) set"
  context_readers :: "nat set"

record execution_request =
  request_binding :: transfer_binding
  request_certificate :: source_certificate
  request_caller :: nat
  request_authority_epoch :: nat
  request_version :: nat

record normal_envelope =
  envelope_id :: nat
  envelope_request :: execution_request

datatype message_route = Validated_Route | Bypass_Route

record message_state =
  consumed_at :: "(nat \<times> source_key) set"
  credit_history :: "transfer_binding list"

datatype message_reply =
    Message_Rejected
  | Duplicate_Credit transfer_binding
  | New_Credit transfer_binding

definition empty_message_state :: message_state where
  "empty_message_state = \<lparr>consumed_at = {}, credit_history = []\<rparr>"

definition current_use_allowed :: "execution_context \<Rightarrow> execution_request \<Rightarrow> bool"
  where
  "current_use_allowed c r \<longleftrightarrow>
     request_authority_epoch r = context_authority_epoch c \<and>
     request_version r = context_version c \<and>
     (request_caller r, request_binding r) \<in> context_permissions c"

definition current_read_allowed :: "execution_context \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  bool" where
  "current_read_allowed c caller version \<longleftrightarrow>
     caller \<in> context_readers c \<and> version = context_version c"

definition credit_marker :: "transfer_binding \<Rightarrow> nat \<times> source_key" where
  "credit_marker b = (binding_destination b, binding_key b)"

definition record_credit :: "transfer_binding \<Rightarrow> message_state \<Rightarrow> message_state" where
  "record_credit b s =
     s\<lparr>consumed_at := insert (credit_marker b) (consumed_at s),
       credit_history := credit_history s @ [b]\<rparr>"

definition restore_message_state :: "transfer_binding list \<Rightarrow> message_state" where
  "restore_message_state records =
     \<lparr>consumed_at = set (map credit_marker records), credit_history = records\<rparr>"

text \<open>The history counts successful destination-credit executions.
  Source debits, record replication, replies and lawful later transfers are
  not new destination credits. The local step records the effect and its
  marker together; correspondence to durable storage is an external obligation.\<close>

end
