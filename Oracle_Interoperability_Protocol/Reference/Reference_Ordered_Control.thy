theory Reference_Ordered_Control
  imports "OIP_Product.Wire_Product_Execution"
begin

datatype reference_disposition =
  Ref_Pending | Ref_Applied | Ref_Explicit_Rejection | Ref_Retained_Refusal

record reference_original_debit =
  original_call :: client_call_id
  original_origin :: source_key
  original_generation :: nat
  original_transport :: authenticated_message_id
  original_packet :: wire_bytes

definition reference_work_key where
  "reference_work_key request = (original_origin request, original_generation request)"

record 'head reference_control =
  control_revision :: nat
  control_head :: "'head option"
  control_writer :: nat
  control_revoked :: "product_principal set"
  control_cancelled :: "authenticated_message_id set"
  control_decisions :: "client_call_id \<Rightarrow> (reference_original_debit \<times> reference_disposition) option"
  control_latest :: "(source_key \<times> nat) \<Rightarrow> client_call_id option"

definition reference_can_deliver where
  "reference_can_deliver request state \<longleftrightarrow>
     fst (original_call request) \<notin> control_revoked state \<and>
     original_transport request \<notin> control_cancelled state \<and>
     (\<forall>call old. control_decisions state call = Some (old, Ref_Pending) \<and>
       original_transport old = original_transport request \<longrightarrow>
       original_packet old = original_packet request)"

definition reference_work_can_start where
  "reference_work_can_start request state \<longleftrightarrow>
    (case control_latest state (reference_work_key request) of None \<Rightarrow> True
     | Some previous \<Rightarrow> fst previous = fst (original_call request) \<and>
        (\<exists>old status. control_decisions state previous = Some (old, status) \<and>
          status \<in> {Ref_Explicit_Rejection, Ref_Retained_Refusal}))"

definition reference_admit_pending where
  "reference_admit_pending observed live request =
    (if observed = live \<and> reference_can_deliver request live \<and>
        reference_work_can_start request live \<and> control_decisions live (original_call request) = None
     then live\<lparr>control_revision := Suc (control_revision live),
        control_decisions := (control_decisions live)(original_call request := Some (request, Ref_Pending)),
        control_latest := (control_latest live)(reference_work_key request := Some (original_call request))\<rparr>
     else live)"

definition reference_order_revoke where
  "reference_order_revoke who state = state\<lparr>control_revision := Suc (control_revision state),
    control_revoked := insert who (control_revoked state)\<rparr>"

definition reference_order_cancel where
  "reference_order_cancel transport state = state\<lparr>control_revision := Suc (control_revision state),
    control_cancelled := insert transport (control_cancelled state)\<rparr>"

definition reference_rotate_writer where
  "reference_rotate_writer writer state =
    (if control_writer state < writer then state\<lparr>control_revision := Suc (control_revision state),
       control_writer := writer\<rparr> else state)"

definition reference_publish_applied where
  "reference_publish_applied observed live request candidate_head =
    (if observed = live \<and> control_decisions live (original_call request) = Some (request, Ref_Pending)
     then live\<lparr>control_revision := Suc (control_revision live), control_head := Some candidate_head,
       control_decisions := (control_decisions live)(original_call request := Some (request, Ref_Applied))\<rparr>
     else live)"

definition reference_publish_refusal where
  "reference_publish_refusal observed live request candidate_head =
    (if observed = live \<and>
        control_decisions live (original_call request) \<in> {None, Some (request, Ref_Pending)}
     then live\<lparr>control_revision := Suc (control_revision live), control_head := Some candidate_head,
       control_decisions := (control_decisions live)(original_call request := Some (request, Ref_Retained_Refusal))\<rparr>
     else live)"

definition reference_close_unresolved where
  "reference_close_unresolved observed live authorized no_receipt may_close_unseen request =
    (if observed = live \<and> authorized \<and> no_receipt \<and>
        fst (original_call request) \<notin> control_revoked live \<and>
        (control_decisions live (original_call request) = Some (request, Ref_Pending) \<or>
         (control_decisions live (original_call request) = None \<and> may_close_unseen \<and>
          control_latest live (reference_work_key request) = None))
     then live\<lparr>control_revision := Suc (control_revision live),
        control_decisions := (control_decisions live)(original_call request := Some (request, Ref_Explicit_Rejection)),
        control_latest := (control_latest live)(reference_work_key request := Some (original_call request))\<rparr>
     else live)"

lemma ordered_control_compares_the_whole_admission_observation:
  assumes "observed \<noteq> live"
  shows "reference_publish_applied observed live request candidate_head = live"
    "reference_publish_refusal observed live request candidate_head = live"
  using assms by (simp_all add: reference_publish_applied_def reference_publish_refusal_def)

lemma revocation_and_cancellation_both_fence_an_earlier_preparation:
  "reference_publish_applied state (reference_order_revoke who state) request candidate =
    reference_order_revoke who state"
  "reference_publish_applied state (reference_order_cancel key state) request candidate =
    reference_order_cancel key state"
proof -
  have changed_revoked: "control_revision (reference_order_revoke who state) = Suc (control_revision state)"
    by (simp add: reference_order_revoke_def)
  have revoked: "state \<noteq> reference_order_revoke who state"
  proof
    assume "state = reference_order_revoke who state"
    then have "control_revision state = control_revision (reference_order_revoke who state)" by simp
    then show False using changed_revoked by simp
  qed
  have changed_cancelled: "control_revision (reference_order_cancel key state) = Suc (control_revision state)"
    by (simp add: reference_order_cancel_def)
  have cancelled: "state \<noteq> reference_order_cancel key state"
  proof
    assume "state = reference_order_cancel key state"
    then have "control_revision state = control_revision (reference_order_cancel key state)" by simp
    then show False using changed_cancelled by simp
  qed
  show "reference_publish_applied state (reference_order_revoke who state) request candidate =
    reference_order_revoke who state"
    by (rule ordered_control_compares_the_whole_admission_observation(1)[OF revoked])
  show "reference_publish_applied state (reference_order_cancel key state) request candidate =
    reference_order_cancel key state"
    by (rule ordered_control_compares_the_whole_admission_observation(1)[OF cancelled])
qed

lemma unresolved_or_applied_work_has_no_new_call:
  assumes "control_latest state (reference_work_key request) = Some previous"
    "control_decisions state previous = Some (old, status)"
    "status = Ref_Pending \<or> status = Ref_Applied"
  shows "\<not> reference_work_can_start request state"
  using assms by (auto simp: reference_work_can_start_def)

lemma resolving_a_published_receipt_cannot_close_the_original:
  assumes "control_decisions state (original_call request) = Some (request, Ref_Applied)"
  shows "reference_close_unresolved state state authorized no_receipt may_close_unseen request = state"
  using assms by (simp add: reference_close_unresolved_def)

lemma a_prior_exact_rejection_preserves_the_head_and_defeats_the_pending_effect:
  fixes closed state request may_close_unseen
  assumes pending: "control_decisions state (original_call request) = Some (request, Ref_Pending)"
    and current: "fst (original_call request) \<notin> control_revoked state"
  defines "closed \<equiv> reference_close_unresolved state state True True may_close_unseen request"
  shows "control_head closed = control_head state"
    "control_decisions closed (original_call request) = Some (request, Ref_Explicit_Rejection)"
    "reference_publish_applied state closed request candidate = closed"
proof -
  show "control_head closed = control_head state"
    using pending current by (simp add: closed_def reference_close_unresolved_def)
  show rejected: "control_decisions closed (original_call request) = Some (request, Ref_Explicit_Rejection)"
    using pending current by (simp add: closed_def reference_close_unresolved_def)
  have "state \<noteq> closed"
  proof
    assume "state = closed"
    then have "control_decisions state (original_call request) = control_decisions closed (original_call request)" by simp
    then show False using pending rejected by simp
  qed
  then show "reference_publish_applied state closed request candidate = closed"
    by (rule ordered_control_compares_the_whole_admission_observation(1))
qed

lemma an_admitted_debit_publishes_without_rechecking_the_delivery_clock:
  assumes pending: "control_decisions state (original_call request) = Some (request, Ref_Pending)"
  shows "control_head (reference_publish_applied state state request candidate) = Some candidate"
    "control_decisions (reference_publish_applied state state request candidate) (original_call request) =
       Some (request, Ref_Applied)"
  using pending by (simp_all add: reference_publish_applied_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordered_control_compares_the_whole_admission_observation
      revocation_and_cancellation_both_fence_an_earlier_preparation unresolved_or_applied_work_has_no_new_call
      resolving_a_published_receipt_cannot_close_the_original
      a_prior_exact_rejection_preserves_the_head_and_defeats_the_pending_effect
      an_admitted_debit_publishes_without_rechecking_the_delivery_clock})
  then () else error "Unexpected oracle in the ordered control model"
\<close>

end
