theory Origin_Decisions
  imports Outcome_Recovery
begin

section \<open>One authoritative slot per original event\<close>

record product_origin_decision =
  origin_binding :: transfer_binding
  origin_kind :: terminal_kind
  origin_epoch :: nat
  origin_commit_position :: nat

record origin_world =
  origin_outcomes :: outcome_world
  origin_debits :: "source_key \<Rightarrow> (transfer_binding \<times> nat) option"
  origin_decisions :: "source_key \<Rightarrow> product_origin_decision option"

definition initial_origin_world where
  "initial_origin_world s = \<lparr>origin_outcomes = initial_outcome_world s,
    origin_debits = (\<lambda>_. None), origin_decisions = (\<lambda>_. None)\<rparr>"

definition decision_matches where
  "decision_matches decision b kind epoch \<longleftrightarrow>
    origin_binding decision = b \<and> origin_kind decision = kind \<and> origin_epoch decision = epoch"

definition existing_decision_matches where
  "existing_decision_matches s b kind epoch \<longleftrightarrow>
    (\<exists>decision. origin_decisions s (binding_key b) = Some decision \<and> decision_matches decision b kind epoch)"

definition terminal_admission where
  "terminal_admission s cert epoch \<longleftrightarrow>
    (let b = statement_binding (certificate_statement cert); key = binding_key b in
      (case binding_operation b of Destination_Credit \<Rightarrow> origin_debits s key = Some (b, epoch)
       | Regulatory_State_Effect action \<Rightarrow> True | _ \<Rightarrow> False) \<and>
      (case kind_from_source (statement_status (certificate_statement cert)) of None \<Rightarrow> False
       | Some kind \<Rightarrow> (case origin_decisions s key of None \<Rightarrow> True
         | Some old \<Rightarrow> decision_matches old b kind epoch)))"

definition certificate_matches_decision where
  "certificate_matches_decision s cert epoch \<longleftrightarrow>
    (case kind_from_source (statement_status (certificate_statement cert)) of None \<Rightarrow> False
     | Some kind \<Rightarrow> existing_decision_matches s (statement_binding (certificate_statement cert)) kind epoch)"

fun origin_intent_allowed where
  "origin_intent_allowed s envelope epoch (Source_Intent r g versions) =
    (let b = request_binding r in
      case origin_debits s (binding_key b) of None \<Rightarrow> epoch = cut_authority_epoch (envelope_cut envelope)
      | Some retained \<Rightarrow> retained = (b, epoch))"
| "origin_intent_allowed s envelope epoch (Certificate_Intent cert) = certificate_matches_decision s cert epoch"
| "origin_intent_allowed s envelope epoch (Deliver_Intent route r) =
    existing_decision_matches s (request_binding r) Confirmed_Decision epoch"
| "origin_intent_allowed s envelope epoch (Return_Intent r g versions) =
    existing_decision_matches s (request_binding r) Reversed_Decision epoch"
| "origin_intent_allowed s envelope epoch (Reconcile_Intent r g versions) =
    existing_decision_matches s (request_binding r) Confirmed_Decision epoch"
| "origin_intent_allowed s envelope epoch (Descendant_Intent r root sender recipient amount) =
    existing_decision_matches s root Confirmed_Decision epoch"
| "origin_intent_allowed s envelope epoch (Reserve_Intent r versions duration) = True"
| "origin_intent_allowed s envelope epoch (Dispatch_Intent r g versions) = True"
| "origin_intent_allowed s envelope epoch (Cancel_Intent r g versions) = True"
| "origin_intent_allowed s envelope epoch (Fence_Intent r g versions) = True"
| "origin_intent_allowed s envelope epoch (Reassign_Intent r duration) = True"
| "origin_intent_allowed s envelope epoch (Write_Intent r g versions value) = True"
| "origin_intent_allowed s envelope epoch (Time_Intent elapsed) = True"
| "origin_intent_allowed s envelope epoch (Data_Read_Intent r) = True"

fun origin_command_allowed where
  "origin_command_allowed s envelope epoch (Client_Terminal cert) = terminal_admission s cert epoch"
| "origin_command_allowed s envelope epoch (Client_Protocol endpoint index intent) = origin_intent_allowed s envelope epoch intent"
| "origin_command_allowed s envelope epoch (Client_Regulatory endpoint index r) =
    existing_decision_matches s (request_binding r) Confirmed_Decision epoch"
| "origin_command_allowed s envelope epoch (Client_Publication key) =
    (\<exists>decision. origin_decisions s key = Some decision \<and> origin_epoch decision = epoch \<and>
       envelope_asset envelope = binding_asset (origin_binding decision))"

definition retain_first_origin_decision where
  "retain_first_origin_decision key decision s =
    (if origin_decisions s key = None then s\<lparr>origin_decisions := (origin_decisions s)(key := Some decision)\<rparr> else s)"

definition retain_first_origin_debit where
  "retain_first_origin_debit b epoch s =
    (if origin_debits s (binding_key b) = None
     then s\<lparr>origin_debits := (origin_debits s)(binding_key b := Some (b, epoch))\<rparr> else s)"

definition retain_actual_origin_result where
  "retain_actual_origin_result command reply epoch position s =
    (case command of Client_Protocol endpoint index intent \<Rightarrow>
        (case intent of Source_Intent r g versions \<Rightarrow>
          if reply = Protocol_Response Source_Debited then retain_first_origin_debit (request_binding r) epoch s else s
        | _ \<Rightarrow> s)
    | Client_Terminal cert \<Rightarrow>
        if reply = Terminal_Recorded \<or> reply = Evidence_Refreshed then
          let b = statement_binding (certificate_statement cert) in
          case kind_from_source (statement_status (certificate_statement cert)) of None \<Rightarrow> s
          | Some kind \<Rightarrow> retain_first_origin_decision (binding_key b)
              \<lparr>origin_binding = b, origin_kind = kind, origin_epoch = epoch, origin_commit_position = position\<rparr> s
        else s
    | _ \<Rightarrow> s)"

lemma origin_metadata_retention_keeps_the_authority_result:
  "origin_outcomes (retain_actual_origin_result command reply epoch position s) = origin_outcomes s"
proof (cases command)
  case (Client_Protocol endpoint index intent)
  then show ?thesis by (cases intent)
    (simp_all add: retain_actual_origin_result_def retain_first_origin_debit_def split: if_splits)
next
  case (Client_Terminal cert)
  then show ?thesis
    by (simp add: retain_actual_origin_result_def retain_first_origin_decision_def Let_def split: option.splits if_splits)
qed (simp_all add: retain_actual_origin_result_def)

context source_attestation
begin

definition submit_origin_call where
  "submit_origin_call permitted verified maintainers registered entry who call_id payload s =
    (let envelope = payload_envelope payload; epoch = payload_origin_epoch payload; cmd = envelope_command envelope;
         previous = origin_outcomes s;
         permitted_origin = (\<lambda>route actor command. permitted route actor command \<and> origin_command_allowed s envelope epoch command);
         next = submit_authoritative_call permitted_origin verified maintainers registered entry who call_id payload previous;
         updated = s\<lparr>origin_outcomes := next\<rparr>
     in if outcome_entries previous call_id \<noteq> None then s
        else case (outcome_entries next call_id, call_authority_results (product_calls (outcome_source next)) call_id) of
          (Some saved, Some (actual, reply, position)) \<Rightarrow>
            if result_payload saved = payload \<and> actual = cmd then retain_actual_origin_result cmd reply epoch position updated else updated
        | _ \<Rightarrow> updated)"

lemma exact_origin_retry_does_not_repeat_an_effect:
  "outcome_entries (origin_outcomes s) call_id \<noteq> None \<Longrightarrow>
    submit_origin_call permitted verified maintainers registered entry who call_id payload s = s"
  by (simp add: submit_origin_call_def Let_def)

lemma conflicting_origin_binding_cannot_change_public_state:
  assumes "\<not> origin_command_allowed s (payload_envelope payload) (payload_origin_epoch payload)
    (envelope_command (payload_envelope payload))"
  shows "outcome_source (origin_outcomes (submit_origin_call permitted verified maintainers registered entry who call_id payload s)) =
    outcome_source (origin_outcomes s)"
proof -
  let ?perm = "\<lambda>route actor command. permitted route actor command \<and>
    origin_command_allowed s (payload_envelope payload) (payload_origin_epoch payload) command"
  have denied: "\<not> ?perm entry who (envelope_command (payload_envelope payload))"
    using assms by simp
  have source: "outcome_source (submit_authoritative_call ?perm verified maintainers registered entry who call_id payload (origin_outcomes s)) =
    outcome_source (origin_outcomes s)"
    by (rule denied_route_cannot_change_the_public_source) (rule denied)
  show ?thesis
    by (simp add: submit_origin_call_def Let_def origin_metadata_retention_keeps_the_authority_result source
        split: option.splits prod.splits if_splits)
qed

end

lemma retain_first_decision_preserves_occupied_slot:
  "origin_decisions s existing = Some old \<Longrightarrow>
    origin_decisions (retain_first_origin_decision key decision s) existing = Some old"
  by (auto simp: retain_first_origin_decision_def)

lemma actual_result_cannot_overwrite_a_decision:
  assumes occupied: "origin_decisions s key = Some old"
  shows "origin_decisions (retain_actual_origin_result command reply epoch position s) key = Some old"
proof (cases command)
  case (Client_Protocol endpoint index intent)
  then show ?thesis using occupied
    by (cases intent) (simp_all add: retain_actual_origin_result_def retain_first_origin_debit_def split: if_splits)
next
  case (Client_Terminal cert)
  then show ?thesis using occupied
    by (simp add: retain_actual_origin_result_def Let_def retain_first_decision_preserves_occupied_slot
        split: option.splits if_splits)
qed (simp_all add: occupied retain_actual_origin_result_def)

context source_attestation
begin

lemma any_origin_entry_keeps_a_committed_decision:
  "origin_decisions s key = Some old \<Longrightarrow>
    origin_decisions (submit_origin_call permitted verified maintainers registered entry who call_id payload s) key = Some old"
  by (auto simp: submit_origin_call_def Let_def intro: actual_result_cannot_overwrite_a_decision
      split: option.splits prod.splits if_splits)

end

lemma one_origin_slot_cannot_confirm_and_reverse:
  "\<not> (existing_decision_matches s b Confirmed_Decision epoch \<and>
         existing_decision_matches s b' Reversed_Decision epoch' \<and> binding_key b = binding_key b')"
proof
  assume clash: "existing_decision_matches s b Confirmed_Decision epoch \<and>
    existing_decision_matches s b' Reversed_Decision epoch' \<and> binding_key b = binding_key b'"
  have same: "binding_key b = binding_key b'" using clash by simp
  obtain confirmed where first: "origin_decisions s (binding_key b) = Some confirmed"
    "origin_kind confirmed = Confirmed_Decision"
    using clash unfolding existing_decision_matches_def decision_matches_def by blast
  obtain reversed where second: "origin_decisions s (binding_key b') = Some reversed"
    "origin_kind reversed = Reversed_Decision"
    using clash unfolding existing_decision_matches_def decision_matches_def by blast
  have "confirmed = reversed" using first(1) second(1) same by simp
  then show False using first(2) second(2) by simp
qed

end
