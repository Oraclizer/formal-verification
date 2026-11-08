theory Reference_Authority_Grants
  imports "OIP_Product.Parallel_Service"
begin

datatype reference_permission =
    Ref_Reserve | Ref_Dispatch | Ref_Debit | Ref_Cancel | Ref_Fence
  | Ref_Preempt | Ref_Observe_Time | Ref_Attest | Ref_Credit | Ref_Refund
  | Ref_Reconcile | Ref_Write | Ref_Publish_Primary | Ref_Spend | Ref_Regulatory

record reference_authority_inputs =
  reference_epoch :: nat
  reference_grants :: "nat \<Rightarrow> (product_principal \<times> lock_entry \<times> reference_permission) set"

fun reference_intent_permission where
  "reference_intent_permission (Reserve_Intent r versions duration) = Some Ref_Reserve"
| "reference_intent_permission (Dispatch_Intent r g versions) = Some Ref_Dispatch"
| "reference_intent_permission (Source_Intent r g versions) = Some Ref_Debit"
| "reference_intent_permission (Cancel_Intent r g versions) = Some Ref_Cancel"
| "reference_intent_permission (Fence_Intent r g versions) = Some Ref_Fence"
| "reference_intent_permission (Reassign_Intent r duration) = Some Ref_Preempt"
| "reference_intent_permission (Write_Intent r g versions v) = Some Ref_Write"
| "reference_intent_permission (Time_Intent elapsed) = Some Ref_Observe_Time"
| "reference_intent_permission (Deliver_Intent route r) = Some Ref_Credit"
| "reference_intent_permission (Return_Intent r g versions) = Some Ref_Refund"
| "reference_intent_permission (Reconcile_Intent r g versions) = Some Ref_Reconcile"
| "reference_intent_permission (Certificate_Intent cert) = None"
| "reference_intent_permission (Descendant_Intent r b sender receiver amount) = Some Ref_Spend"
| "reference_intent_permission (Data_Read_Intent r) = None"

fun reference_command_permission where
  "reference_command_permission (Client_Protocol endpoint i intent) =
    map_option (Pair endpoint) (reference_intent_permission intent)"
| "reference_command_permission (Client_Terminal cert) =
    Some (fst (binding_key (statement_binding (certificate_statement cert))), Ref_Attest)"
| "reference_command_permission (Client_Publication key) = Some (fst key, Ref_Publish_Primary)"
| "reference_command_permission (Client_Regulatory endpoint i r) = Some (endpoint, Ref_Regulatory)"

definition reference_permitted_at where
  "reference_permitted_at inputs entry who command \<longleftrightarrow>
    (case reference_command_permission command of None \<Rightarrow> False
     | Some (endpoint, permission) \<Rightarrow>
         (who, entry, permission) \<in> reference_grants inputs endpoint)"

lemma regulatory_execution_consumes_its_own_live_grant:
  "reference_permitted_at inputs entry actor (Client_Protocol endpoint index (Descendant_Intent request root sender receiver amount))
     \<longleftrightarrow> (actor, entry, Ref_Spend) \<in> reference_grants inputs endpoint"
  "reference_permitted_at inputs entry actor (Client_Regulatory endpoint index request)
     \<longleftrightarrow> (actor, entry, Ref_Regulatory) \<in> reference_grants inputs endpoint"
  by (simp_all add: reference_permitted_at_def)

lemma a_debit_only_grant_cannot_enable_regulated_spending:
  "\<not> reference_permitted_at
    \<lparr>reference_epoch = epoch, reference_grants = (\<lambda>_. {(actor,entry,Ref_Debit)})\<rparr>
    entry actor (Client_Protocol endpoint index (Descendant_Intent request root sender receiver amount))"
  by (simp add: reference_permitted_at_def)

record reference_authority_snapshot =
  reference_product :: retained_product
  reference_inputs :: reference_authority_inputs

definition reference_records_epoch where
  "reference_records_epoch records =
    product_authority_epoch (retained_authority (retained_source records))"

definition reference_grants_fit where
  "reference_grants_fit registered records inputs \<longleftrightarrow>
    reference_epoch inputs = reference_records_epoch records \<and>
    (\<forall>endpoint. endpoint \<notin> registered \<longrightarrow> reference_grants inputs endpoint = {})"

fun reference_reconfiguration where
  "reference_reconfiguration (Service_Handover owner successor maintainer proposal) = True"
| "reference_reconfiguration (Service_Maintenance (Exact_Install who epoch changes sessions)) = True"
| "reference_reconfiguration action = False"

definition select_reference_grants where
  "select_reference_grants registered authenticated action supplied before records =
    (if reference_records_epoch records = reference_records_epoch (reference_product before)
     then Some (reference_inputs before)
     else case supplied of None \<Rightarrow> None
       | Some inputs \<Rightarrow>
           if reference_reconfiguration action \<and>
             reference_records_epoch (reference_product before) < reference_records_epoch records \<and>
             authenticated action inputs \<and> reference_grants_fit registered records inputs
           then Some inputs else None)"

lemma grant_selection_keeps_the_old_table_at_the_same_epoch:
  assumes "reference_records_epoch records = reference_records_epoch (reference_product before)"
  shows "select_reference_grants registered authenticated action supplied before records =
    Some (reference_inputs before)"
  using assms by (simp add: select_reference_grants_def)

lemma grant_selection_at_a_new_epoch_consumes_the_exact_authorized_installation:
  assumes selected: "select_reference_grants registered authenticated action supplied before records = Some inputs"
    and changed: "reference_records_epoch records \<noteq> reference_records_epoch (reference_product before)"
  shows "supplied = Some inputs \<and> reference_reconfiguration action \<and> authenticated action inputs \<and>
    reference_records_epoch (reference_product before) < reference_records_epoch records \<and>
    reference_grants_fit registered records inputs"
  using selected changed by (auto simp: select_reference_grants_def split: option.splits if_splits)

lemma grant_selection_preserves_binding:
  assumes "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and "select_reference_grants registered authenticated action supplied before records = Some inputs"
  shows "reference_grants_fit registered records inputs"
  using assms by (auto simp: select_reference_grants_def reference_grants_fit_def split: option.splits if_splits)

context source_attestation
begin

definition service_at_reference_snapshot where
  "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
     authenticated connection action supplied before =
    (if reference_grants_fit registered (reference_product before) (reference_inputs before)
     then
       (let result = schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
          legal_grant order_verified spend_grant spend_verified read_permitted
          (reference_permitted_at (reference_inputs before)) verified maintainers registered verified_ack
          connection action (reference_product before)
        in case select_reference_grants registered authenticated action supplied before (fst result) of
           None \<Rightarrow> (before, None)
         | Some inputs \<Rightarrow> (\<lparr>reference_product = fst result, reference_inputs = inputs\<rparr>, Some (snd result)))
     else (before, None))"

lemma reference_service_success_preserves_epoch_and_grant_binding:
  assumes "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
     authenticated connection action supplied before = (after, Some reply)"
  shows "reference_grants_fit registered (reference_product after) (reference_inputs after)"
  using assms by (auto simp: service_at_reference_snapshot_def Let_def
    split: option.splits if_splits intro: grant_selection_preserves_binding)

lemma reference_service_refusal_leaves_the_exact_snapshot:
  assumes "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
     legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
     authenticated connection action supplied before = (after, None)"
  shows "after = before"
  using assms by (auto simp: service_at_reference_snapshot_def Let_def split: option.splits if_splits)

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms regulatory_execution_consumes_its_own_live_grant
      a_debit_only_grant_cannot_enable_regulated_spending grant_selection_keeps_the_old_table_at_the_same_epoch
      grant_selection_at_a_new_epoch_consumes_the_exact_authorized_installation
      grant_selection_preserves_binding
      source_attestation.reference_service_success_preserves_epoch_and_grant_binding
      source_attestation.reference_service_refusal_leaves_the_exact_snapshot})
  then () else error "Unexpected oracle in retained authority grant consumption"
\<close>

end
