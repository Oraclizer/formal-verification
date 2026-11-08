theory Wire_Code_Source_Identity
  imports Wire_Code_Fixed_Call_Request
begin

record code_source_identity_snapshot =
  source_identity_cut :: product_cut
  source_identity_directory :: identity_directory
  source_identity_sessions :: "product_session_id \<Rightarrow> product_session_binding option"
  source_identity_endpoints :: "nat set"

definition code_source_identity_projects_to_product :: "code_source_identity_snapshot \<Rightarrow> product_world \<Rightarrow> bool" where
  "code_source_identity_projects_to_product observed source \<longleftrightarrow>
    source_identity_cut observed = current_product_cut source \<and>
    source_identity_sessions observed = product_sessions (product_durable source)"

definition code_source_active_identity ::
  "('token \<Rightarrow> session_proof \<Rightarrow> registered_identity option) \<Rightarrow>
    'token \<Rightarrow> session_proof \<Rightarrow> code_source_identity_snapshot \<Rightarrow> registered_identity option" where
  "code_source_active_identity authenticate_session token proof observed =
    (case authenticate_session token proof of None \<Rightarrow> None | Some identity \<Rightarrow>
      if source_identity_directory observed (identity_principal identity) \<noteq> Some identity \<or>
         proof_epoch proof \<noteq> cut_authority_epoch (source_identity_cut observed) \<or>
         source_identity_sessions observed (proof_session proof) \<noteq>
           Some \<lparr>session_principal = identity_principal identity,session_epoch = cut_authority_epoch (source_identity_cut observed)\<rparr>
      then None else Some identity)"

fun code_source_claim_target :: "code_source_product_action \<Rightarrow> nat" where
  "code_source_claim_target (Code_Source_Ordinary_Action payload) = source_payload_endpoint payload"
| "code_source_claim_target (Code_Source_Legal_Action_Data Code_Source_Emission payload order) =
    fst (source_binding_origin (source_payload_binding payload))"
| "code_source_claim_target (Code_Source_Legal_Action_Data Code_Receiving_Commit payload order) =
    source_binding_destination (source_payload_binding payload)"
| "code_source_claim_target (Code_Source_Spend_Action_Data payload authorization) =
    source_binding_destination (source_payload_binding payload)"

definition code_source_authorize_call ::
  "('token \<Rightarrow> session_proof \<Rightarrow> registered_identity option) \<Rightarrow> endpoint_policy \<Rightarrow>
    (registered_identity \<Rightarrow> session_proof \<Rightarrow> nat \<Rightarrow> endpoint_use \<Rightarrow>
      client_call_id \<Rightarrow> code_source_product_action \<Rightarrow> bool) \<Rightarrow>
    'token \<Rightarrow> session_proof \<Rightarrow> code_source_action_request \<Rightarrow> endpoint_use \<Rightarrow>
    code_source_identity_snapshot \<Rightarrow> registered_identity option" where
  "code_source_authorize_call authenticate_session policy verify_signed_call token proof request operation observed =
    (case code_source_active_identity authenticate_session token proof observed of None \<Rightarrow> None | Some identity \<Rightarrow>
      let action = source_request_action request; payload = code_source_action_payload action;
          target = source_request_target request; call_id = source_request_id request
      in if identity_principal identity \<noteq> fst call_id \<or>
            source_payload_caller payload \<noteq> identity_principal identity \<or>
            source_payload_session payload \<noteq> proof_session proof \<or>
            cut_authority_epoch (source_payload_cut payload) \<noteq> proof_epoch proof \<or>
            code_source_claim_target action \<noteq> target \<or>
            target \<notin> source_identity_endpoints observed \<or>
            \<not> policy identity target (source_binding_asset (source_payload_binding payload)) operation (proof_epoch proof) \<or>
            \<not> verify_signed_call identity proof target operation call_id action
         then None else Some identity)"

theorem the_source_active_identity_is_the_existing_current_model_identity_check:
  assumes projection: "code_source_identity_projects_to_product observed source"
  shows "code_source_active_identity authenticate_session token proof observed = Some identity \<longleftrightarrow>
    authenticate_session token proof = Some identity \<and>
    active_identity (source_identity_directory observed) identity proof source"
  using projection
  by (auto simp: code_source_active_identity_def code_source_identity_projects_to_product_def
    active_identity_def split: option.splits if_splits)

theorem a_source_authorized_call_consumes_its_exact_current_session_namespace_and_typed_action:
  assumes authorized: "code_source_authorize_call authenticate_session policy verify_signed_call token proof request operation observed = Some identity"
  shows "code_source_active_identity authenticate_session token proof observed = Some identity"
    "identity_principal identity = fst (source_request_id request)"
    "source_payload_caller (code_source_action_payload (source_request_action request)) = identity_principal identity"
    "source_payload_session (code_source_action_payload (source_request_action request)) = proof_session proof"
    "cut_authority_epoch (source_payload_cut (code_source_action_payload (source_request_action request))) = proof_epoch proof"
    "code_source_claim_target (source_request_action request) = source_request_target request"
    "source_request_target request \<in> source_identity_endpoints observed"
    "policy identity (source_request_target request)
       (source_binding_asset (source_payload_binding (code_source_action_payload (source_request_action request)))) operation (proof_epoch proof)"
    "verify_signed_call identity proof (source_request_target request) operation (source_request_id request) (source_request_action request)"
  using authorized
  by (auto simp: code_source_authorize_call_def Let_def split: option.splits if_splits)

lemma the_source_signature_adapter_receives_the_whole_fixed_typed_action:
  assumes denied: "\<not> verify_signed_call identity proof (source_request_target request) operation
    (source_request_id request) (source_request_action request)"
    and current: "code_source_active_identity authenticate_session token proof observed = Some identity"
  shows "code_source_authorize_call authenticate_session policy verify_signed_call token proof request operation observed = None"
  using denied current by (simp add: code_source_authorize_call_def Let_def)

lemma the_source_known_endpoint_guard_is_an_explicit_additional_path_check:
  assumes "source_request_target request \<notin> source_identity_endpoints observed"
  shows "code_source_authorize_call authenticate_session policy verify_signed_call token proof request operation observed = None"
  using assms by (auto simp: code_source_authorize_call_def Let_def split: option.splits)

lemma source_authorize_call_does_not_replace_the_fresh_expected_cut_coherence_check:
  "code_source_authorize_call authenticate_session policy verify_signed_call token proof
      (request\<lparr>source_request_expected := supplied_cut\<rparr>) operation observed =
    code_source_authorize_call authenticate_session policy verify_signed_call token proof request operation observed"
  by (cases "code_source_active_identity authenticate_session token proof observed")
     (simp_all add: code_source_authorize_call_def Let_def)

theorem an_authorized_materialized_call_keeps_the_received_principal_and_current_identity:
  assumes materialized: "code_materialize_source_call target core = Inr (Some request)"
    and authorized: "code_source_authorize_call authenticate_session policy verify_signed_call token proof request operation observed = Some identity"
    and projection: "code_source_identity_projects_to_product observed source"
  shows "identity_principal identity = wire_principal core"
    "active_identity (source_identity_directory observed) identity proof source"
proof -
  have caller: "identity_principal identity = fst (source_request_id request)"
    by (rule a_source_authorized_call_consumes_its_exact_current_session_namespace_and_typed_action(2)[OF authorized])
  have namespace: "fst (source_request_id request) = wire_principal core"
    by (rule a_materialized_call_keeps_the_authenticated_caller_namespace[OF materialized])
  show "identity_principal identity = wire_principal core" using caller namespace by simp
  have current: "code_source_active_identity authenticate_session token proof observed = Some identity"
    by (rule a_source_authorized_call_consumes_its_exact_current_session_namespace_and_typed_action(1)[OF authorized])
  have link: "code_source_active_identity authenticate_session token proof observed = Some identity \<longleftrightarrow>
      authenticate_session token proof = Some identity \<and>
      active_identity (source_identity_directory observed) identity proof source"
    by (rule the_source_active_identity_is_the_existing_current_model_identity_check[OF projection])
  have model: "authenticate_session token proof = Some identity \<and>
      active_identity (source_identity_directory observed) identity proof source"
    by (rule iffD1[OF link current])
  show "active_identity (source_identity_directory observed) identity proof source" by (rule conjunct2[OF model])
qed

text \<open>
  Source: identity.rs active_identity/authorize_call and Action::claim.
  The authenticate_session result and verify_signed_call are explicit
  security-provider observations, not a whole consume/authorization=true
  input. Directory/current epoch/session/namespace/target/endpoint/policy
  checks are visible here. Provider token claims, installed policy hash,
  exact original-byte signing preimage and curve verification must still
  be connected to their actual source implementation; this file does not
  declare those whole provider operations proved primitives.
  The source has an explicit registered-endpoint test. The old identity
  predicate omits that field, so it is retained as a named additional path
  check rather than silently assumed. authorize_call does not itself test
  request.expected: the fresh retained-result/availability/cut ordering and
  supplied-versus-signed cut coherence belong to the later current entry.
\<close>

end
