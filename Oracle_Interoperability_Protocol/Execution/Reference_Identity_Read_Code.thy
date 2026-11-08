theory Reference_Identity_Read_Code
  imports "OIP_Reference_Profile.Reference_Entry_Closure"
begin

record ('cache, 'records) rust_identity_read_state =
  rust_read_directory :: "nat \<Rightarrow> registered_identity option"
  rust_read_sessions :: "nat \<Rightarrow> (nat \<times> nat) option"
  rust_read_authority_epoch :: nat
  rust_read_endpoints :: "nat set"
  rust_read_grants :: "(nat \<times> nat \<times> identity_read_request \<times> nat) set"
  rust_read_wire_cache :: 'cache
  rust_read_records :: 'records

datatype 'reply rust_identity_read_reply = Rust_Identity_Read_Rejected | Rust_Identity_Observation 'reply

definition rust_identity_read_gate where
  "rust_identity_read_gate target_matches authenticate verify_read token proof target request code \<longleftrightarrow>
    (case authenticate token of None \<Rightarrow> False | Some identity \<Rightarrow>
      let principal = identity_principal identity; epoch = proof_epoch proof in
       rust_read_directory code principal = Some identity \<and> epoch = rust_read_authority_epoch code \<and>
       rust_read_sessions code (proof_session proof) = Some (principal,epoch) \<and>
       target_matches target request \<and> target \<in> rust_read_endpoints code \<and>
       (principal,target,request,epoch) \<in> rust_read_grants code \<and> verify_read identity proof target request)"

definition rust_identity_read_consume where
  "rust_identity_read_consume target_matches authenticate verify_read observe token proof target request code =
    (if rust_identity_read_gate target_matches authenticate verify_read token proof target request code
     then observe code else (code,Rust_Identity_Read_Rejected))"

definition rust_identity_read_matches where
  "rust_identity_read_matches directory policy target_matches code source \<longleftrightarrow>
    rust_read_directory code = directory \<and>
    rust_read_authority_epoch code = cut_authority_epoch (current_product_cut source) \<and>
    rust_read_sessions code = map_option (\<lambda>session. (session_principal session,session_epoch session)) \<circ>
       product_sessions (product_durable source) \<and>
    (\<forall>identity target request epoch. policy identity target request epoch =
      (target_matches target request \<and> target \<in> rust_read_endpoints code \<and>
       (identity_principal identity,target,request,epoch) \<in> rust_read_grants code))"

lemma the_rust_directory_session_target_and_scope_compute_the_model_read_gate:
  assumes related: "rust_identity_read_matches directory policy target_matches code source"
  shows "rust_identity_read_gate target_matches authenticate verify_read token proof target request code =
    identity_read_allowed directory policy authenticate verify_read token proof target request source"
proof -
  have session: "rust_read_sessions code (proof_session proof) = Some (principal,epoch) \<longleftrightarrow>
      product_sessions (product_durable source) (proof_session proof) =
        Some \<lparr>session_principal = principal,session_epoch = epoch\<rparr>" for principal epoch
    using related by (cases "product_sessions (product_durable source) (proof_session proof)")
       (auto simp: rust_identity_read_matches_def)
  show ?thesis using related session
    by (cases "authenticate token") (auto simp: rust_identity_read_gate_def identity_read_allowed_def
       rust_identity_read_matches_def active_identity_def Let_def)
qed

context source_attestation
begin

theorem a_rust_read_outside_the_selected_session_scope_refines_the_actual_reference_refusal:
  fixes live source connection before
  defines "live \<equiv> reopen_retained_product connection (reference_product before)"
    and "source \<equiv> identity_source live"
  assumes initial: "rust_identity_read_matches directory read_policy target_matches code source"
    and current: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and stored: "records_match (rust_read_records code) (reference_product before)"
    and caller: "authenticate token = Some identity"
    and no_grant: "(identity_principal identity,target,request,proof_epoch proof) \<notin> rust_read_grants code"
  shows "let (native,answer) = rust_identity_read_consume target_matches authenticate verify_read observe token proof target request code;
     (model,reply) = service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
       legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
       authenticated connection (Service_Read token proof target request cache) supplied before
    in rust_identity_read_matches directory read_policy target_matches native
         (identity_source (reopen_retained_product connection (reference_product model))) \<and>
       records_match (rust_read_records native) (reference_product model) \<and>
       rust_read_wire_cache native = rust_read_wire_cache code \<and> rust_read_records native = rust_read_records code \<and>
       answer = Rust_Identity_Read_Rejected \<and> reply = Some (Scheduled_Endpoint (Service_Read_Result Identity_Read_Rejected))"
proof -
  have rust: "\<not> rust_identity_read_gate target_matches authenticate verify_read token proof target request code"
    using caller no_grant by (simp add: rust_identity_read_gate_def Let_def)
  have same: "rust_identity_read_gate target_matches authenticate verify_read token proof target request code =
       identity_read_allowed directory read_policy authenticate verify_read token proof target request source"
    by (rule the_rust_directory_session_target_and_scope_compute_the_model_read_gate[OF initial])
  have model: "\<not> identity_read_allowed directory read_policy authenticate verify_read token proof target request source"
    using rust same by simp
  note refused = an_actual_denied_reference_read_preserves_the_snapshot_and_refuses_every_cache[OF current model[unfolded source_def live_def]]
  show ?thesis using initial stored rust refused
    by (simp add: rust_identity_read_consume_def source_def live_def Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_rust_directory_session_target_and_scope_compute_the_model_read_gate
      source_attestation.a_rust_read_outside_the_selected_session_scope_refines_the_actual_reference_refusal})
  then () else error "Unexpected oracle in native identity read correspondence"
\<close>

end
