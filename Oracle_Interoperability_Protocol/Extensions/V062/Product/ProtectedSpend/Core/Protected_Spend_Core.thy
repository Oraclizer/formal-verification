theory Protected_Spend_Core
  imports "OIP_Reference_Execution.Reference_Freeze_Code"
    "OIP_Product.Freeze_Interval"
begin

datatype ps_route = PS_Normal | PS_Administrative | PS_Adapter | PS_Force_Inclusion
datatype ps_kind = PS_Ordinary | PS_Recover | PS_Seize | PS_Confiscate | PS_Liquidate

record ps_binding =
  ps_origin :: source_key
  ps_asset :: nat
  ps_owner :: nat
  ps_destination :: nat
  ps_receiver :: nat
  ps_root_amount :: nat

record ps_scope =
  ps_root :: ps_binding
  ps_sender :: nat
  ps_recipient :: nat
  ps_amount :: nat
  ps_kind :: ps_kind

record ps_enforcement =
  ps_order_scope :: ps_scope
  ps_officer :: nat
  ps_jurisdiction :: nat
  ps_legal_basis :: nat
  ps_assets :: "nat list"
  ps_prior_seizure :: "source_key option"
  ps_appeal_deadline :: "nat option"

record ps_grant =
  ps_grant_route :: ps_route
  ps_grant_actor :: nat
  ps_grant_epoch :: nat
  ps_grant_scope :: ps_scope
  ps_grant_jurisdiction :: nat
  ps_grant_basis :: nat

record ps_payload =
  ps_message :: nat
  ps_caller :: nat
  ps_session :: nat
  ps_payload_cut :: product_cut
  ps_origin_epoch :: nat
  ps_reference :: nat
  ps_scope :: ps_scope

record ps_call =
  ps_route :: ps_route
  ps_actor :: nat
  ps_call_id :: client_call_id
  ps_expected :: product_cut
  ps_payload :: ps_payload
  ps_enforcement :: "ps_enforcement option"

record ps_root_slot =
  ps_slot_binding :: ps_binding
  ps_slot_epoch :: nat
  ps_decision_kind :: "terminal_kind option"
  ps_decision_position :: "nat option"
  ps_settled :: "nat option"
  ps_published :: "nat option"

record ps_reservation =
  ps_reserved :: ps_binding
  ps_holder :: nat
  ps_generation :: nat
  ps_expires :: nat
  ps_phase :: nat
  ps_pending :: nat

record ps_legal_event =
  ps_legal_binding :: ps_binding
  ps_legal_epoch :: nat
  ps_legal_officer :: nat
  ps_legal_jurisdiction :: nat
  ps_legal_basis_value :: nat
  ps_emitted_position :: nat
  ps_applied_position :: "nat option"
  ps_legal_published :: "nat option"

record ps_seizure =
  ps_seizure_key :: source_key
  ps_seizure_freeze :: source_key
  ps_seizure_deadline :: "nat option"

datatype ps_reply = PS_Spend_Executed source_key nat | PS_Spend_Rejected | PS_Spend_Busy | PS_Spend_Unavailable

record ps_state =
  ps_epoch :: nat
  ps_revision :: nat
  ps_clock :: nat
  ps_up :: bool
  ps_available :: bool
  ps_sessions :: "(nat \<times> (nat \<times> nat)) list"
  ps_modes :: "((nat \<times> nat) \<times> reg_state) list"
  ps_balances :: "((nat \<times> nat \<times> nat) \<times> nat) list"
  ps_funding :: "((source_key \<times> (nat \<times> nat \<times> nat)) \<times> nat) list"
  ps_roots :: "(source_key \<times> ps_root_slot) list"
  ps_reservations :: "(source_key \<times> ps_reservation) list"
  ps_active :: "(nat \<times> source_key) list"
  ps_evidence :: "(nat \<times> (ps_binding \<times> terminal_kind)) list"
  ps_legal_events :: "(source_key \<times> ps_legal_event) list"
  ps_active_freezes :: "(nat \<times> source_key) list"
  ps_active_seizures :: "(nat \<times> ps_seizure) list"
  ps_spend_grants :: "ps_grant list"
  ps_spend_receipts :: "(client_call_id \<times> (ps_payload \<times> ps_enforcement option \<times> ps_reply)) list"
  ps_legal_ids :: "client_call_id list"
  ps_ordinary_ids :: "client_call_id list"
  ps_sync_ids :: "client_call_id list"
  ps_journal :: "(client_call_id \<times> nat \<times> nat) list"

definition ps_put where
  "ps_put p5_key p5_value p5_rows = (p5_key,p5_value) # filter (\<lambda>(p5_old,p5_entry). p5_old \<noteq> p5_key) p5_rows"

definition ps_get where
  "ps_get p5_rows p5_key = (case map_of p5_rows p5_key of None \<Rightarrow> 0 | Some p5_value \<Rightarrow> p5_value)"

definition ps_cut where
  "ps_cut p5_state = \<lparr>cut_authority_epoch = ps_epoch p5_state,cut_revision = ps_revision p5_state\<rparr>"

definition ps_holder_account where
  "ps_holder_account p5_root p5_holder = (ps_destination p5_root,ps_asset p5_root,p5_holder)"

definition ps_mode_protected where
  "ps_mode_protected p5_mode \<longleftrightarrow> p5_mode \<in> {FROZEN,SEIZED,CONFISCATED}"

lemma ps_reuses_the_public_protected_mode:
  "ps_mode_protected p5_mode = protected_freeze_mode p5_mode"
  by (simp add: ps_mode_protected_def protected_freeze_mode_def)

definition ps_exact_root where
  "ps_exact_root p5_payload p5_state \<longleftrightarrow>
    (let p5_root = ps_root (ps_scope p5_payload) in
      case map_of (ps_roots p5_state) (ps_origin p5_root) of None \<Rightarrow> False
      | Some p5_slot \<Rightarrow> ps_slot_binding p5_slot = p5_root \<and>
          ps_slot_epoch p5_slot = ps_origin_epoch p5_payload \<and>
          ps_decision_kind p5_slot = Some Confirmed_Decision \<and>
          ps_decision_position p5_slot = Some (ps_reference p5_payload) \<and>
          ps_settled p5_slot \<noteq> None \<and> ps_published p5_slot \<noteq> None)"

definition ps_confiscation_ready where
  "ps_confiscation_ready p5_order p5_mode p5_state \<longleftrightarrow>
    (let p5_asset = ps_asset (ps_root (ps_order_scope p5_order)) in
      case (map_of (ps_active_freezes p5_state) p5_asset,map_of (ps_active_seizures p5_state) p5_asset) of
        (Some p5_freeze,Some p5_seizure) \<Rightarrow>
          ps_seizure_freeze p5_seizure = p5_freeze \<and>
          ps_prior_seizure p5_order = Some (ps_seizure_key p5_seizure) \<and>
          p5_mode \<in> {SEIZED,CONFISCATED} \<and>
          (case ps_appeal_deadline p5_order of None \<Rightarrow> False | Some p5_deadline \<Rightarrow>
            ps_seizure_deadline p5_seizure = Some p5_deadline \<and> p5_deadline \<le> ps_clock p5_state)
      | _ \<Rightarrow> False)"

definition ps_enforcement_coordinates where
  "ps_enforcement_coordinates p5_require_mode p5_call p5_mode p5_state =
    (let p5_scope = ps_scope (ps_payload p5_call) in
      case (ps_kind p5_scope,ps_enforcement p5_call) of
        (PS_Ordinary,None) \<Rightarrow> if p5_require_mode \<and> ps_mode_protected p5_mode then None else Some (0,0)
      | (PS_Ordinary,Some p5_order) \<Rightarrow> None
      | (p5_kind,Some p5_order) \<Rightarrow>
          if ps_order_scope p5_order = p5_scope \<and> ps_officer p5_order = ps_actor p5_call \<and>
             ps_legal_basis p5_order \<noteq> 0 \<and> ps_asset (ps_root p5_scope) \<in> set (ps_assets p5_order) \<and>
             (p5_kind \<noteq> PS_Confiscate \<or> ps_confiscation_ready p5_order p5_mode p5_state)
          then Some (ps_jurisdiction p5_order,ps_legal_basis p5_order) else None
      | _ \<Rightarrow> None)"

definition ps_granted where
  "ps_granted p5_call p5_jurisdiction p5_basis p5_state \<longleftrightarrow>
    \<lparr>ps_grant_route = ps_route p5_call,ps_grant_actor = ps_actor p5_call,ps_grant_epoch = ps_epoch p5_state,
      ps_grant_scope = ps_scope (ps_payload p5_call),ps_grant_jurisdiction = p5_jurisdiction,ps_grant_basis = p5_basis\<rparr>
    \<in> set (ps_spend_grants p5_state)"

definition ps_spend_funding where
  "ps_spend_funding p5_scope p5_state =
    (let p5_root = ps_root p5_scope; p5_amount = ps_amount p5_scope;
         p5_source = ps_holder_account p5_root (ps_sender p5_scope);
         p5_destination = ps_holder_account p5_root (ps_recipient p5_scope);
         p5_from = (ps_origin p5_root,p5_source); p5_to = (ps_origin p5_root,p5_destination)
     in if p5_amount = 0 \<or> Suc (ps_revision p5_state) \<ge> 2^64 then None
        else case map_of (ps_funding p5_state) p5_from of None \<Rightarrow> None | Some p5_funded \<Rightarrow>
          if p5_funded < p5_amount \<or> ps_get (ps_balances p5_state) p5_source < p5_amount then None
          else if p5_source = p5_destination then Some (p5_state\<lparr>ps_revision := Suc (ps_revision p5_state)\<rparr>,ps_revision p5_state)
          else if ps_get (ps_funding p5_state) p5_to + p5_amount \<ge> 2^64 \<or>
                  ps_get (ps_balances p5_state) p5_destination + p5_amount \<ge> 2^64 then None
          else Some (p5_state\<lparr>ps_revision := Suc (ps_revision p5_state),
            ps_funding := ps_put p5_to (ps_get (ps_funding p5_state) p5_to + p5_amount)
              (ps_put p5_from (p5_funded - p5_amount) (ps_funding p5_state)),
            ps_balances := ps_put p5_destination (ps_get (ps_balances p5_state) p5_destination + p5_amount)
              (ps_put p5_source (ps_get (ps_balances p5_state) p5_source - p5_amount) (ps_balances p5_state))\<rparr>,
            ps_revision p5_state))"

definition ps_apply_spend where
  "ps_apply_spend p5_require_mode p5_call p5_state =
    (let p5_payload = ps_payload p5_call; p5_scope = ps_scope p5_payload; p5_root = ps_root p5_scope in
      if ps_expected p5_call \<noteq> ps_cut p5_state \<or> ps_payload_cut p5_payload \<noteq> ps_cut p5_state
      then (p5_state,PS_Spend_Busy)
      else case map_of (ps_modes p5_state) (ps_destination p5_root,ps_asset p5_root) of None \<Rightarrow> (p5_state,PS_Spend_Rejected)
      | Some p5_mode \<Rightarrow> case ps_enforcement_coordinates p5_require_mode p5_call p5_mode p5_state of
          None \<Rightarrow> (p5_state,PS_Spend_Rejected)
        | Some (p5_jurisdiction,p5_basis) \<Rightarrow>
            if \<not> ps_granted p5_call p5_jurisdiction p5_basis p5_state \<or> \<not> ps_exact_root p5_payload p5_state
            then (p5_state,PS_Spend_Rejected)
            else case ps_spend_funding p5_scope p5_state of None \<Rightarrow> (p5_state,PS_Spend_Rejected)
              | Some (p5_after,p5_position) \<Rightarrow> (p5_after,PS_Spend_Executed (ps_origin p5_root) p5_position))"

definition ps_access where
  "ps_access p5_verified p5_call p5_state \<longleftrightarrow> p5_verified \<and>
    fst (ps_call_id p5_call) = ps_actor p5_call \<and> ps_caller (ps_payload p5_call) = ps_actor p5_call \<and>
    map_of (ps_sessions p5_state) (ps_session (ps_payload p5_call)) = Some (ps_actor p5_call,ps_epoch p5_state)"

definition ps_submit_spend where
  "ps_submit_spend p5_require_mode p5_verified p5_call p5_state =
    (if \<not> ps_access p5_verified p5_call p5_state then (p5_state,PS_Spend_Rejected)
     else if \<not> ps_up p5_state then (p5_state,PS_Spend_Unavailable)
     else case map_of (ps_spend_receipts p5_state) (ps_call_id p5_call) of
       Some (p5_payload,p5_order,p5_reply) \<Rightarrow>
         (p5_state,if p5_payload = ps_payload p5_call \<and> p5_order = ps_enforcement p5_call then p5_reply else PS_Spend_Rejected)
     | None \<Rightarrow> if ps_call_id p5_call \<in> set (ps_legal_ids p5_state @ ps_ordinary_ids p5_state @ ps_sync_ids p5_state)
       then (p5_state,PS_Spend_Rejected)
       else let (p5_after,p5_reply) = (if ps_available p5_state then ps_apply_spend p5_require_mode p5_call p5_state
                else (p5_state,PS_Spend_Unavailable));
                p5_journal = (if ps_revision p5_after > ps_revision p5_state then ps_journal p5_after @
                   [(ps_call_id p5_call,ps_destination (ps_root (ps_scope (ps_payload p5_call))),ps_revision p5_state)]
                   else ps_journal p5_after)
            in (p5_after\<lparr>ps_journal := p5_journal,ps_spend_receipts := ps_put (ps_call_id p5_call)
                 (ps_payload p5_call,ps_enforcement p5_call,p5_reply) (ps_spend_receipts p5_after)\<rparr>,p5_reply))"

definition ps_source_protected where
  "ps_source_protected p5_binding p5_state \<longleftrightarrow>
    (case map_of (ps_modes p5_state) (fst (ps_origin p5_binding),ps_asset p5_binding) of
      None \<Rightarrow> False | Some p5_mode \<Rightarrow> ps_mode_protected p5_mode)"

lemma ps_ordinary_protected_body_refuses_without_changing_the_state:
  assumes "ps_expected p5_call = ps_cut p5_state" "ps_payload_cut (ps_payload p5_call) = ps_cut p5_state"
    "map_of (ps_modes p5_state) (ps_destination (ps_root (ps_scope (ps_payload p5_call))),ps_asset (ps_root (ps_scope (ps_payload p5_call)))) = Some p5_mode"
    "ps_mode_protected p5_mode" "ps_kind (ps_scope (ps_payload p5_call)) = PS_Ordinary"
  shows "ps_apply_spend True p5_call p5_state = (p5_state,PS_Spend_Rejected)"
  using assms by (simp add: ps_apply_spend_def ps_enforcement_coordinates_def Let_def split: option.splits)

theorem ps_exact_one_mode_guard_removal_reaches_the_same_funding_body:
  assumes p5_cut: "ps_expected p5_call = ps_cut p5_state" "ps_payload_cut (ps_payload p5_call) = ps_cut p5_state"
    and p5_mode: "map_of (ps_modes p5_state) (ps_destination (ps_root (ps_scope (ps_payload p5_call))),ps_asset (ps_root (ps_scope (ps_payload p5_call)))) = Some p5_protected"
      "ps_mode_protected p5_protected"
    and p5_ordinary: "ps_kind (ps_scope (ps_payload p5_call)) = PS_Ordinary" "ps_enforcement p5_call = None"
    and p5_authority: "ps_granted p5_call 0 0 p5_state" "ps_exact_root (ps_payload p5_call) p5_state"
    and p5_funding: "ps_spend_funding (ps_scope (ps_payload p5_call)) p5_state = Some (p5_after,p5_position)"
  shows "ps_apply_spend True p5_call p5_state = (p5_state,PS_Spend_Rejected)"
    "ps_apply_spend False p5_call p5_state = (p5_after,PS_Spend_Executed (ps_origin (ps_root (ps_scope (ps_payload p5_call)))) p5_position)"
  using assms by (simp_all add: ps_apply_spend_def ps_enforcement_coordinates_def Let_def)

theorem ps_lawful_recovery_consumes_the_same_current_root_and_funding:
  assumes "ps_expected p5_call = ps_cut p5_state" "ps_payload_cut (ps_payload p5_call) = ps_cut p5_state"
    "map_of (ps_modes p5_state) (ps_destination (ps_root (ps_scope (ps_payload p5_call))),ps_asset (ps_root (ps_scope (ps_payload p5_call)))) = Some p5_mode"
    "ps_kind (ps_scope (ps_payload p5_call)) = PS_Recover" "ps_enforcement p5_call = Some p5_order"
    "ps_order_scope p5_order = ps_scope (ps_payload p5_call)" "ps_officer p5_order = ps_actor p5_call"
    "ps_legal_basis p5_order \<noteq> 0" "ps_asset (ps_root (ps_scope (ps_payload p5_call))) \<in> set (ps_assets p5_order)"
    "ps_granted p5_call (ps_jurisdiction p5_order) (ps_legal_basis p5_order) p5_state"
    "ps_exact_root (ps_payload p5_call) p5_state"
    "ps_spend_funding (ps_scope (ps_payload p5_call)) p5_state = Some (p5_after,p5_position)"
  shows "ps_apply_spend True p5_call p5_state =
    (p5_after,PS_Spend_Executed (ps_origin (ps_root (ps_scope (ps_payload p5_call)))) p5_position)"
  using assms by (simp add: ps_apply_spend_def ps_enforcement_coordinates_def Let_def)

lemma ps_funding_body_preserves_regulation_and_exact_root_records:
  assumes "ps_spend_funding p5_scope p5_state = Some (p5_after,p5_position)"
  shows "ps_modes p5_after = ps_modes p5_state" "ps_roots p5_after = ps_roots p5_state"
    "ps_revision p5_after = Suc (ps_revision p5_state)" "p5_position = ps_revision p5_state"
  using assms by (auto simp: ps_spend_funding_def Let_def split: option.splits if_splits)

lemma ps_current_access_is_required_before_a_retained_spend_receipt:
  "\<not> ps_access p5_verified p5_call p5_state \<Longrightarrow>
    ps_submit_spend p5_check p5_verified p5_call p5_state = (p5_state,PS_Spend_Rejected)"
  by (simp add: ps_submit_spend_def)

context source_attestation
begin
lemmas ps_existing_frozen_wrapper_correspondence = fresh_frozen_spend_refines_the_governed_spend_state_and_reply
lemmas ps_existing_protected_balance_frame = protected_ordinary_spending_cannot_change_authoritative_balances
lemmas ps_existing_lawful_exact_root = lawful_enforcement_consumes_the_exact_confirmed_root
lemmas ps_existing_no_thaw_interval = ordinary_spend_after_freeze_without_thaw_is_rejected
end

text \<open>
  This leaf spells out the native spend branch and wrapper, not a supplied
  verdict table. The no-thaw/current-authority hypotheses remain explicit.
  CommitRef has only a position; origin epoch and the current authority cut are
  separate exact checks. The single mutant removes only !mode.protected() from
  the Ordinary/None branch. Current credentials, verification callback, current
  cut, grant, exact confirmed/published root and funding checks remain. Source
  Dispatch/Debit protection is a separate entry obligation, not this mutation.
  An operational seed child must construct the funded root and completed Freeze
  from genesis and establish the conditional premises; this Core alone is not
  a concrete four-row execution result or general Rust refinement proof.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ps_ordinary_protected_body_refuses_without_changing_the_state
      ps_exact_one_mode_guard_removal_reaches_the_same_funding_body
      ps_lawful_recovery_consumes_the_same_current_root_and_funding
      ps_funding_body_preserves_regulation_and_exact_root_records
      ps_current_access_is_required_before_a_retained_spend_receipt})
  then () else error "Unexpected oracle in protected spend native branch"
\<close>

end
