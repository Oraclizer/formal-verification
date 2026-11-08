theory Reference_Freeze_Code
  imports "OIP_Reference_Profile.Reference_Freeze_Spender"
begin

datatype rust_spend_reply = Rust_Spend_Rejected | Rust_Spend_Busy | Rust_Spend_Unavailable

record rust_spend_image =
  rust_spend_cut :: product_cut
  rust_spend_modes :: "(nat \<times> nat) \<Rightarrow> reg_state option"
  rust_spend_source :: "source_account \<Rightarrow> nat"
  rust_spend_destination :: "destination_account \<Rightarrow> nat"
  rust_spend_funded :: "(source_key \<times> destination_account) \<Rightarrow> nat"
  rust_spend_receipts :: "client_call_id \<Rightarrow> (product_call_payload \<times> rust_spend_reply) option"

definition rust_spend_money_matches where
  "rust_spend_money_matches code ledger \<longleftrightarrow>
    rust_spend_source code = source_units ledger \<and>
    rust_spend_destination code = destination_units ledger \<and>
    rust_spend_funded code = funded_units ledger"

fun observe_rust_spend where
  "observe_rust_spend Spend_Blocked entry = Some Rust_Spend_Rejected"
| "observe_rust_spend (Spend_Checked Checked_Execution_Busy) entry = Some Rust_Spend_Busy"
| "observe_rust_spend (Spend_Checked Checked_Execution_Unavailable) entry = Some Rust_Spend_Unavailable"
| "observe_rust_spend (Spend_Checked Checked_Execution_Rejected) entry = Some Rust_Spend_Rejected"
| "observe_rust_spend (Spend_Checked Forwarded_At_Checked_Cut) entry =
    (if map_option result_outcome entry = Some Authority_Rejected then Some Rust_Spend_Rejected else None)"

definition rust_spend_entry_matches where
  "rust_spend_entry_matches code key ledger entry \<longleftrightarrow>
    rust_spend_money_matches code ledger \<and>
    map_option (\<lambda>(payload, reply). \<lparr>result_payload = payload, result_outcome =
      (case reply of Rust_Spend_Rejected \<Rightarrow> Authority_Rejected
        | Rust_Spend_Busy \<Rightarrow> Authority_Busy | Rust_Spend_Unavailable \<Rightarrow> Authority_Unavailable)\<rparr>)
      (rust_spend_receipts code key) = entry"

text \<open>The selected slice stops before the unprotected spending body. None marks that body,
not a refusal. The wrapper retains an exact receipt after apply_spend.\<close>
definition rust_submit_ordinary_spend where
  "rust_submit_ordinary_spend access up available occupied expected key payload domain asset code =
    (if \<not> access then Some (code, Rust_Spend_Rejected)
     else if \<not> up then Some (code, Rust_Spend_Unavailable)
     else case rust_spend_receipts code key of Some (original, reply) \<Rightarrow>
       Some (code, if original = payload then reply else Rust_Spend_Rejected)
     | None \<Rightarrow> if occupied then Some (code, Rust_Spend_Rejected) else
       let reply = if \<not> available then Some Rust_Spend_Unavailable
         else if expected \<noteq> rust_spend_cut code \<or> envelope_cut (payload_envelope payload) \<noteq> rust_spend_cut code
         then Some Rust_Spend_Busy
         else if rust_spend_modes code (domain, asset) \<in> {None, Some FROZEN, Some SEIZED, Some CONFISCATED}
         then Some Rust_Spend_Rejected else None
       in map_option (\<lambda>r. (code\<lparr>rust_spend_receipts := (rust_spend_receipts code)(key := Some (payload,r))\<rparr>, r)) reply)"

context source_attestation
begin

theorem fresh_frozen_spend_refines_the_governed_spend_state_and_reply:
  fixes live actor key payload code reads authority origins outcomes source envelope command cfg expected
  defines "reads \<equiv> regulated_read_world live"
    and "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
    and "command \<equiv> envelope_command envelope"
    and "cfg \<equiv> authoritative_read_core authority"
    and "expected \<equiv> observed_product_cut authority"
  assumes ordinary: "command = Client_Protocol endpoint index (Descendant_Intent r root sender recipient amount)"
    "binding_operation (request_binding r) = Ordinary_Transfer_Effect"
    and valid: "valid_state (receiver_snapshot (core_regulatory cfg))"
    and frozen: "get_reg_state (receiver_snapshot (core_regulatory cfg))
      (binding_destination root) (binding_asset (request_binding r)) = Some FROZEN"
    and fresh: "product_new_call actor key envelope source"
    and authentic: "verified actor key payload"
    and exact: "envelope_cut envelope = expected"
    and unrecorded: "outcome_entries outcomes key = None"
      "legal_receipts (regulated_orders live) key = None" "spend_receipts live key = None"
    and admitted: "permitted (regulatory_lock_entry Regulatory_Normal) actor command"
      "registered_lock_envelope registered envelope"
      "lock_envelope_admitted actor envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
    and related: "rust_spend_entry_matches code key (machine_state (core_parent cfg)) (outcome_entries outcomes key)"
    and bound_cut: "rust_spend_cut code = expected"
    and bound_mode: "rust_spend_modes code (binding_destination root, binding_asset (request_binding r)) =
      get_reg_state (receiver_snapshot (core_regulatory cfg)) (binding_destination root) (binding_asset (request_binding r))"
  shows "let model_result = submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
        Regulatory_Normal actor expected key payload None live;
      after = read_authority (regulated_read_world (fst model_result));
      entry = outcome_entries (origin_outcomes (settlement_primary after)) key
    in \<exists>native reply. rust_submit_ordinary_spend True True True False expected key payload
          (binding_destination root) (binding_asset (request_binding r)) code = Some (native, reply) \<and>
       rust_spend_entry_matches native key (machine_state (core_parent (authoritative_read_core after))) entry \<and>
       observe_rust_spend (snd model_result) entry = Some reply"
proof -
  let ?checked = "execute_at_checked_cut permitted verified maintainers registered verified_ack
        (regulatory_lock_entry Regulatory_Normal) actor expected key payload reads"
  let ?model = "submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
        Regulatory_Normal actor expected key payload None live"
  let ?next = "read_authority (fst ?checked)"
  let ?entry = "outcome_entries (origin_outcomes (settlement_primary ?next)) key"
  note path = source_def outcomes_def origins_def authority_def envelope_def command_def
  have access: "result_access_bound verified actor key payload outcomes"
    using fresh authentic by (simp add: result_access_bound_def product_new_call_def envelope_def source_def)
  have ready: "call_local_status (product_calls source) = Endpoint_Up"
    "call_connection (product_calls source) = Authority_Connected"
    using fresh by (simp_all add: product_new_call_def)
  have available: "read_authority_available reads"
    using ready by (simp add: read_authority_available_def exact_calls_def outcome_calls_def path)
  have up: "call_local_status (exact_calls authority) = Endpoint_Up"
    using ready(1) by (simp add: exact_calls_def outcome_calls_def path)
  have allowed: "governed_spend_is_admitted grant spend_verified actor payload None (governed_legal (regulated_orders live))"
    using ordinary by (simp add: governed_spend_is_admitted_def command_def envelope_def)
  have forwarded: "snd ?checked = Forwarded_At_Checked_Cut"
    using access available exact
    by (simp add: execute_at_checked_cut_def expected_def path Let_def)
  have computed: "regulated_read_world (fst ?model) = fst ?checked"
    "snd ?model = Spend_Checked Forwarded_At_Checked_Cut"
    using access available up unrecorded allowed forwarded
    by (simp_all add: submit_governed_spend_def run_spend_effect_def replace_regulated_reads_def
        regulated_read_world_def legal_underlying_outcomes_def path reads_def Let_def)
  have frozen_checked: "?entry = Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr> \<and>
    machine_state (core_parent (call_authority_state (outcome_calls (origin_outcomes (settlement_primary ?next))))) =
      machine_state (core_parent cfg)"
    unfolding expected_def cfg_def path authority_def
    using the_checked_frozen_spend_records_refusal_and_preserves_the_ledger
      [where reads=reads and verified=verified and verified_ack=verified_ack and permitted=permitted
         and maintainers=maintainers and registered=registered and entry="regulatory_lock_entry Regulatory_Normal",
       OF ordinary[unfolded path] valid[unfolded cfg_def path] frozen[unfolded cfg_def path]
          fresh[unfolded path] authentic unrecorded(1)[unfolded path] admitted[unfolded path]]
    by (simp add: Let_def)
  have model_state: "?entry = Some \<lparr>result_payload = payload, result_outcome = Authority_Rejected\<rparr>"
    "machine_state (core_parent (authoritative_read_core ?next)) = machine_state (core_parent cfg)"
    using frozen_checked by (simp_all add: authoritative_read_core_def exact_calls_def)
  let ?native = "code\<lparr>rust_spend_receipts := (rust_spend_receipts code)(key := Some (payload, Rust_Spend_Rejected))\<rparr>"
  have empty: "rust_spend_receipts code key = None"
    using related unrecorded(1) by (cases "rust_spend_receipts code key") (simp_all add: rust_spend_entry_matches_def)
  have native: "rust_submit_ordinary_spend True True True False expected key payload
      (binding_destination root) (binding_asset (request_binding r)) code = Some (?native, Rust_Spend_Rejected)"
    using empty bound_cut bound_mode frozen exact
    by (simp add: rust_submit_ordinary_spend_def envelope_def Let_def)
  show ?thesis unfolding Let_def
    using computed model_state native related
    by (intro exI[of _ ?native] exI[of _ Rust_Spend_Rejected])
       (simp add: rust_spend_entry_matches_def rust_spend_money_matches_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.fresh_frozen_spend_refines_the_governed_spend_state_and_reply})
  then () else error "Unexpected oracle in frozen spend code correspondence"
\<close>

end
