theory Pending_Lock_Export
  imports "OIP_Pending_Lock_Model.Pending_Lock_G0" "HOL-Library.Code_Target_Nat"
begin

definition pl_bit :: "bool \<Rightarrow> nat" where
  "pl_bit value = (if value then 1 else 0)"

fun pl_phase_word :: "pl_phase \<Rightarrow> nat" where
  "pl_phase_word PL_Held = 0"
| "pl_phase_word PL_Dispatched = 1"
| "pl_phase_word PL_Pending = 2"
| "pl_phase_word PL_Credited = 3"
| "pl_phase_word PL_Reconciled = 4"
| "pl_phase_word PL_Refunded = 5"
| "pl_phase_word PL_Closed = 6"

fun pl_reply_word :: "pl_reply \<Rightarrow> nat" where
  "pl_reply_word PL_Rejected = 0"
| "pl_reply_word PL_Closed_Reply = 1"
| "pl_reply_word PL_Preempted = 2"
| "pl_reply_word PL_Time_Observed = 3"
| "pl_reply_word PL_Reconciled_Reply = 4"

fun pl_optional_word :: "nat option \<Rightarrow> nat" where
  "pl_optional_word None = 0"
| "pl_optional_word (Some value) = value"

definition pl_binding_words where
  "pl_binding_words binding =
    [fst (pl_origin binding),snd (pl_origin binding),pl_asset binding,pl_owner binding,
      pl_destination binding,pl_recipient binding,pl_amount binding]"

type_synonym pl_integer_state =
  "integer list \<times> integer list \<times> integer list list \<times> integer list list \<times> integer list list"

definition pl_state_view :: "pl_state \<Rightarrow> pl_integer_state" where
  "pl_state_view state =
    (map integer_of_nat (pl_binding_words (pls_binding state) @
      [pls_epoch state,pls_revision state,pls_clock state,pls_holder state,pls_generation state,pls_expires state,
       pl_phase_word (pls_phase state),pl_bit (pls_exists state),pls_source state,pls_destination_balance state,
       pls_root_funding state,pl_pending state,pl_visible_mass state,pl_bit (pls_terminal state \<noteq> None),
       pl_optional_word (pls_terminal state)]),
     map integer_of_nat (pls_footprint state),
     map (\<lambda>(asset,(domain,event)). map integer_of_nat [asset,domain,event]) (pls_active state),
     map (\<lambda>(asset,version). map integer_of_nat [asset,version]) (pls_versions state),
     map (\<lambda>(reference,(binding,kind)). map integer_of_nat
       ([reference,if kind = PL_Confirmed then 1 else 2] @ pl_binding_words binding)) (pls_evidence state))"

fun pl_command_words :: "pl_command \<Rightarrow> nat list" where
  "pl_command_words (PL_Cancel generation) = [0,generation,0]"
| "pl_command_words (PL_Fence generation) = [1,generation,0]"
| "pl_command_words (PL_Preempt duration) = [2,duration,0]"
| "pl_command_words (PL_Time elapsed) = [3,elapsed,0]"
| "pl_command_words (PL_Reconcile generation reference) = [4,generation,reference]"

definition pl_request_view where
  "pl_request_view request = map integer_of_nat
    (pl_binding_words (plr_binding request) @
     [plr_actor request,plr_caller request,plr_session request,plr_endpoint request,
       plr_cut_epoch request,plr_cut_revision request,plr_route request,pl_bit (plr_verified request)] @
     pl_command_words (plr_command request) @
     (case plr_credential request of None \<Rightarrow> [0,0,0,0,0,0,0]
      | Some token \<Rightarrow> [1,plc_asset token,fst (plc_origin token),snd (plc_origin token),
          plc_holder token,plc_generation token,plc_epoch token]))"

definition pl_gate_view where
  "pl_gate_view request state = map integer_of_nat
    ([pl_bit (pl_request_admitted request state),pl_bit (pl_effect_credential request state),
      pl_bit (pl_receipt_credential request state)] @
     (case plr_command request of PL_Reconcile generation reference \<Rightarrow>
        [1,pl_bit (pl_exact_confirmed state reference)] | _ \<Rightarrow> [0,0]))"

definition pl_previous_bound_after where
  "pl_previous_bound_after before after =
    (let token = pl_seed_credential (pls_binding before) (pls_holder before) (pls_generation before) (pls_epoch before);
         request = pl_fresh_request after (pls_holder before) (if pls_holder before = 7 then 1 else 2)
           (PL_Cancel (pls_generation before)) (Some token)
     in pl_bound_credential request after (pls_generation before))"

type_synonym pl_integer_result =
  "integer list \<times> integer list \<times> pl_integer_state \<times> pl_integer_state \<times> integer list \<times> integer list"

definition pl_integer_case where
  "pl_integer_case require_credit item = map_option
    (\<lambda>(before,request,after,reply).
      (map integer_of_nat [plcase_id item,pl_reply_word reply,pl_bit (before = after),
         pl_bit (pl_previous_bound_after before after)],
       pl_request_view request,pl_state_view before,pl_state_view after,
       pl_gate_view request before,pl_gate_view request after)) (pl_run_case require_credit item)"

definition pl_normal_integer_cases :: "unit \<Rightarrow> pl_integer_result option list" where
  "pl_normal_integer_cases ignored = map (pl_integer_case True) pl_cases"

definition pl_mutant_integer_case :: "unit \<Rightarrow> pl_integer_result option" where
  "pl_mutant_integer_case ignored = pl_integer_case False pl_case_reconcile_confirmed_not_credited"

definition pl_concrete_witnesses :: "unit \<Rightarrow> bool list" where
  "pl_concrete_witnesses ignored = [pl_uncredited_guard_ready,pl_credit_guard_removal_witness,
    pl_exact_credit_positive_witness,pl_old_token_after_preempt_witness]"

lemma pl_integer_prefix_failure_has_no_native_reply:
  "pl_case_before item = None \<Longrightarrow> pl_integer_case flag item = None"
  by (simp add: pl_integer_case_def pl_run_case_def)

text \<open>
  Reply tags describe native Ledger replies, not OIP Response codes. Every
  before-state is separately emitted for source prefix validation. Effect and
  receipt fields are credential predicates only, not complete authorization
  or durable result claims. Normal cases and the one phase-guard mutant remain
  separate. The four concrete witness values are standalone observations.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms pl_integer_prefix_failure_has_no_native_reply})
  then () else error "Unexpected oracle in pending-lock export"
\<close>

code_reserved (SML) before

export_code pl_normal_integer_cases pl_mutant_integer_case pl_concrete_witnesses
  in SML module_name OIP_Pending_Lock file_prefix "oip_pending_lock"

end
