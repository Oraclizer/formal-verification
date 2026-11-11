theory Wire_Code_Funded_Source_Projection
  imports "OIP_Message_Code.Wire_Code_Debit_Resolution" "OIP_Reference_Profile.Reference_Source_Accounts"
begin

record 'head code_source_funded_image =
  source_funded_image :: "'head reference_funded_product_image"
  source_recorded_reservations :: "source_key \<Rightarrow> code_source_receipt_reservation option"

definition code_funded_source_core :: "'head code_source_funded_image \<Rightarrow> finality_core" where
  "code_funded_source_core snapshot =
    retained_core (retained_source (reference_product
      (image_authority (funded_product (source_funded_image snapshot)))))"

definition code_funded_source_machine :: "'head code_source_funded_image \<Rightarrow> reservation_machine" where
  "code_funded_source_machine snapshot = core_parent (code_funded_source_core snapshot)"

definition code_funded_source_accounts :: "'head code_source_funded_image \<Rightarrow> reference_source_accounts" where
  "code_funded_source_accounts snapshot = exact_source_accounts (source_funded_image snapshot)"

definition code_funded_source_cut :: "'head code_source_funded_image \<Rightarrow> product_cut" where
  "code_funded_source_cut snapshot = current_product_cut (reopen_retained_source Authority_Connected
    (retained_source (reference_product (image_authority (funded_product (source_funded_image snapshot))))))"

definition code_source_binding_projects_to_model :: "code_source_binding \<Rightarrow> transfer_binding \<Rightarrow> bool" where
  "code_source_binding_projects_to_model source_binding model_binding \<longleftrightarrow>
    binding_key model_binding = source_binding_origin source_binding \<and>
    binding_asset model_binding = source_binding_asset source_binding \<and>
    binding_amount model_binding = source_binding_amount source_binding \<and>
    binding_destination model_binding = source_binding_destination source_binding \<and>
    binding_recipient model_binding = source_binding_recipient source_binding"

definition code_source_recorded_reservations_project :: "'head code_source_funded_image \<Rightarrow> bool" where
  "code_source_recorded_reservations_project snapshot \<longleftrightarrow>
    (\<forall>key. case (source_recorded_reservations snapshot key,
          reservation_at (machine_state (code_funded_source_machine snapshot)) key) of
       (None,None) \<Rightarrow> True
     | (Some source_stored,Some model_stored) \<Rightarrow>
         code_source_binding_projects_to_model (source_reservation_binding source_stored) (reservation_binding model_stored) \<and>
         source_reservation_holder source_stored = reservation_worker model_stored \<and>
         source_reservation_generation source_stored = reservation_generation model_stored \<and>
         source_reservation_deadline source_stored = reservation_deadline model_stored \<and>
         source_reservation_active source_stored = active_reservation_phase (reservation_phase model_stored)
     | _ \<Rightarrow> False)"

definition code_source_funded_image_is_coherent :: "'head code_source_funded_image \<Rightarrow> bool" where
  "code_source_funded_image_is_coherent snapshot \<longleftrightarrow>
    reference_funded_image_is_coherent (source_funded_image snapshot) \<and>
    code_source_recorded_reservations_project snapshot"

definition code_model_debit_binding_matches_native :: "wire_native_call \<Rightarrow> transfer_binding \<Rightarrow> bool" where
  "code_model_debit_binding_matches_native native binding \<longleftrightarrow>
    binding_key binding = native_origin native \<and> binding_asset binding = native_asset native \<and>
    binding_amount binding = native_amount native \<and> binding_destination binding = native_destination native \<and>
    binding_recipient binding = native_recipient native \<and> binding_source_epoch binding = native_origin_epoch native \<and>
    binding_operation binding = Destination_Credit"

definition code_model_debit_request ::
  "lock_context \<Rightarrow> wire_native_call \<Rightarrow> reservation_state \<Rightarrow> execution_request option" where
  "code_model_debit_request authority_view native financial =
    (case reservation_at financial (native_origin native) of None \<Rightarrow> None
     | Some stored \<Rightarrow> let binding = reservation_binding stored in
       if \<not> code_model_debit_binding_matches_native native binding then None
       else Some \<lparr>request_binding = binding,
         request_certificate = \<lparr>certificate_statement =
           \<lparr>statement_binding = binding,statement_status = Observed\<rparr>,
           certificate_epoch = native_origin_epoch native,certificate_signers = [],certificate_signature = 0\<rparr>,
         request_caller = fst (native_id native),
         request_authority_epoch = cut_authority_epoch (native_cut native),
         request_version = context_version (lock_authority authority_view)\<rparr>)"

definition code_model_version_at :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat" where
  "code_model_version_at versions asset = (case map_of versions asset of None \<Rightarrow> 0 | Some version \<Rightarrow> version)"

lemma a_paired_source_projection_reads_the_machine_and_accounts_of_one_funded_image:
  assumes coherent: "code_source_funded_image_is_coherent snapshot"
  shows "source_accounts_match_the_pool (code_funded_source_accounts snapshot)
    (machine_state (code_funded_source_machine snapshot))"
  using coherent
  by (simp add: code_source_funded_image_is_coherent_def reference_funded_image_is_coherent_def
    code_funded_source_accounts_def code_funded_source_machine_def code_funded_source_core_def
    capture_reference_view_def capture_snapshot_def)

theorem a_fixed_debit_request_selects_the_binding_from_its_actual_model_reservation:
  assumes projected: "code_model_debit_request authority_view native financial = Some request"
  obtains stored :: asset_reservation
  where "reservation_at financial (native_origin native) = Some stored"
    "request_binding request = reservation_binding stored"
    "code_model_debit_binding_matches_native native (request_binding request)"
    "request_caller request = fst (native_id native)"
    "request_authority_epoch request = cut_authority_epoch (native_cut native)"
    "request_version request = context_version (lock_authority authority_view)"
  using projected
  by (auto simp: code_model_debit_request_def Let_def split: option.splits if_splits)

lemma the_fixed_debit_projection_preserves_all_model_representable_native_binding_fields:
  assumes "code_model_debit_request authority_view native financial = Some request"
  shows "binding_key (request_binding request) = native_origin native"
    "binding_asset (request_binding request) = native_asset native"
    "binding_amount (request_binding request) = native_amount native"
    "binding_destination (request_binding request) = native_destination native"
    "binding_recipient (request_binding request) = native_recipient native"
    "binding_source_epoch (request_binding request) = native_origin_epoch native"
    "binding_operation (request_binding request) = Destination_Credit"
  using assms
  by (auto simp: code_model_debit_request_def code_model_debit_binding_matches_native_def Let_def
    split: option.splits if_splits)

lemma the_fixed_debit_projection_satisfies_the_existing_signed_binding_relation:
  assumes "code_model_debit_request authority_view native financial = Some request"
  shows "signed_debit_request_matches native request"
  using assms
  by (auto simp: code_model_debit_request_def code_model_debit_binding_matches_native_def
    signed_debit_request_matches_def Let_def split: option.splits if_splits)

lemma source_debit_does_not_consume_the_model_only_certificate:
  fixes request :: execution_request
  shows "execute_source_effect authority_view (request\<lparr>request_certificate := certificate\<rparr>) generation versions machine =
    execute_source_effect authority_view request generation versions machine"
proof -
  have allowed: "current_use_allowed (lock_authority authority_view) (request\<lparr>request_certificate := certificate\<rparr>) =
      current_use_allowed (lock_authority authority_view) request"
    by (simp add: current_use_allowed_def)
  have owned: "owns_current_reservation authority_view (request\<lparr>request_certificate := certificate\<rparr>) generation versions state =
      owns_current_reservation authority_view request generation versions state" for state
    by (simp add: owns_current_reservation_def owns_recorded_reservation_def allowed)
  have metadata: "metadata_permission authority_view (request\<lparr>request_certificate := certificate\<rparr>) domain =
      metadata_permission authority_view request domain" for domain
    by (cases "get_reg_state (lock_metadata authority_view) domain (binding_asset (request_binding request))";
        cases "binding_operation (request_binding request)")
       (simp_all add: metadata_permission_def allowed)
  have observation: "record_observation (request\<lparr>request_certificate := certificate\<rparr>) reply observed_machine =
      record_observation request reply observed_machine" for reply observed_machine
    by (simp add: record_observation_def)
  show ?thesis
    by (auto simp: execute_source_effect_def allowed owned metadata observation Let_def)
qed

lemma a_model_source_debit_commits_exactly_its_source_financial_event:
  assumes "execute_source_effect authority_view request generation versions before = (after,Source_Debited)"
  shows "machine_state after = apply_reservation_event (Source_Effect_Event (request_binding request)) (machine_state before)"
    "machine_journal after = machine_journal before @ [Source_Effect_Event (request_binding request)]"
  using assms
  by (auto simp: execute_source_effect_def record_observation_def commit_reservation_event_def Let_def split: if_splits)

lemma a_model_debit_without_a_source_effect_preserves_the_financial_state:
  assumes "execute_source_effect authority_view request generation versions before = (after,reply)"
    "reply \<noteq> Source_Debited"
  shows "machine_state after = machine_state before"
  using assms
  by (auto simp: execute_source_effect_def record_observation_def commit_reservation_event_def Let_def split: if_splits)

text \<open>
  The request comes from the reservation in this same model image, with no
  arbitrary attach or request callback. The source Binding has an owner;
  the frozen transfer_binding does not. The owner is retained in the source
  reservation and used by the funded step, rather than added to the frozen
  binding. The binding source epoch/operation/separator and current context
  version are model coordinates. A missing or incompatible registered model
  binding remains Projection_Pending, not an invented Rust rejection.
  The synthetic Observed certificate is not a claim of a source attestation:
  Source_Intent's financial consumer ignores it by the equality above. This
  projection is restricted to Debit and must not be reused for credit,
  refund, terminal evidence, signature preimages or receipt equality.
  The actual Rust-to-paired-image relation remains a reception obligation.
\<close>

end
