theory EAB_Binding_Cutover
  imports DOSP_Degree.Promotion_Cutover EAB_Primary_Repair
    Preemptive_Lock_Correctness.Reservation_Progress
begin

record metered_source_state =
  registered_asset :: nat
  degree_state :: "nat cutover_state"
  source_authority :: eab_primary_authority

datatype metered_credit_reply =
    Wrong_Asset
  | Cutover_Refused cutover_error
  | Unavailable_Publication_Sequence
  | Source_Reply finality_reply
  | Credit_Awaiting_Publication finality_reply
  | Credit_Metered billing_entry

datatype pending_resolution = Reconcile_Credit | Release_Reversal

abbreviation credit_core :: "metered_source_state \<Rightarrow> finality_core" where
  "credit_core s \<equiv> terminal_authority (source_authority s)"

abbreviation transfer_commit :: "transfer_binding \<Rightarrow> nat flow_action" where
  "transfer_commit b \<equiv> Commit_From (fst (binding_key b)) (binding_destination b) (binding_amount b)"

definition promotion_assets :: "nat flow_policy \<Rightarrow> metered_source_state \<Rightarrow> nat set" where
  "promotion_assets policy s =
    insert (registered_asset s)
      (\<Union>origin\<in>allowed_sources policy.
        set (lock_dependencies (current_lock_view (credit_core s) origin) (registered_asset s)))"

definition promotion_locks_clear :: "nat flow_policy \<Rightarrow> metered_source_state \<Rightarrow> bool" where
  "promotion_locks_clear policy s \<longleftrightarrow>
    (\<forall>asset\<in>promotion_assets policy s.
      asset_owner (machine_state (core_parent (credit_core s))) asset = None)"

definition promote_settled_asset ::
  "nat flow_policy \<Rightarrow> promotion_grants \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    metered_source_state \<Rightarrow> metered_source_state \<times> cutover_result"
where
  "promote_settled_asset policy grants epoch version s =
    (if promotion_locks_clear policy s \<and> promotion_allowed grants (degree_state s) epoch version
     then (s\<lparr>degree_state := (degree_state s)\<lparr>route_metadata := promoted_metadata epoch version\<rparr>\<rparr>,
        transition_result.Accepted Promotion_Finalized)
     else (s, transition_result.Rejected Ineligible_Promotion))"

lemma settled_asset_promotion_projects_to_cutover:
  assumes "promote_settled_asset policy grants epoch version s = (t, transition_result.Accepted Promotion_Finalized)"
  shows "cutover_step policy grants (degree_state s) (Confirm_Promotion epoch version)
      (transition_result.Accepted Promotion_Finalized) (degree_state t) \<and>
    promotion_locks_clear policy s \<and> source_authority t = source_authority s"
  using assms by (auto simp: promote_settled_asset_def intro: cutover_step.Promote split: if_splits)

lemma a_live_lock_blocks_promotion:
  assumes "asset \<in> promotion_assets policy s"
    "asset_owner (machine_state (core_parent (credit_core s))) asset = Some key"
  shows "promote_settled_asset policy grants epoch version s = (s, transition_result.Rejected Ineligible_Promotion)"
  using assms by (auto simp: promote_settled_asset_def promotion_locks_clear_def)

context source_attestation
begin

definition meter_source_credit ::
  "nat flow_policy \<Rightarrow> cutover_metadata \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> message_route
    \<Rightarrow> execution_request \<Rightarrow> metered_source_state \<Rightarrow>
    metered_source_state \<times> metered_credit_reply"
where
  "meter_source_credit policy ticket epoch index sequence route r s =
    (let b = request_binding r;
         view = degree_state s;
         id = prod_encode (binding_key b);
         action = transfer_commit b
     in if binding_asset b \<noteq> registered_asset s \<or> binding_operation b \<noteq> Destination_Credit then (s, Wrong_Asset)
        else if ticket \<noteq> route_metadata view then (s, Cutover_Refused Stale_Ticket)
        else if \<not> can_commit policy view id ticket action then (s, Cutover_Refused Disallowed_Route)
        else if publication_slots (source_authority s) sequence \<noteq> None \<or>
                binding_key b \<in> core_published (credit_core s)
          then (s, Unavailable_Publication_Sequence)
        else
          let delivery = Invoke_Protocol (binding_destination b) epoch index (Deliver_Intent route r);
              reply = snd (core_result delivery (credit_core s));
              delivered_authority = (source_authority s)\<lparr>terminal_authority := finality_step delivery (credit_core s)\<rparr>;
              source_next = s\<lparr>source_authority := delivered_authority\<rparr>
          in if reply = Protocol_Response (Delivery_Response (New_Credit b)) then
                let published = publish_at_sequence (binding_key b) sequence delivered_authority
                in if snd published = Primary_Published then
                    let entry = billing_record id ticket action;
                        next = fst (evaluate_flow policy (chosen_path ticket) True (binding_state view) action)
                    in (s\<lparr>source_authority := fst published, degree_state := view\<lparr>binding_state := next,
                        billing_history := billing_history view @ [entry]\<rparr>\<rparr>, Credit_Metered entry)
                   else (source_next, Credit_Awaiting_Publication (snd published))
             else (source_next, Source_Reply reply))"

lemma stale_registry_ticket_does_not_deliver_or_meter:
  assumes "binding_asset (request_binding r) = registered_asset s"
    "binding_operation (request_binding r) = Destination_Credit"
    "ticket \<noteq> route_metadata (degree_state s)"
  shows "meter_source_credit policy ticket epoch index sequence route r s = (s, Cutover_Refused Stale_Ticket)"
  using assms by (simp add: meter_source_credit_def Let_def)

lemma unpublished_credit_keeps_degree_and_billing:
  assumes "meter_source_credit policy ticket epoch index sequence route r s = (t, result)"
    "\<forall>entry. result \<noteq> Credit_Metered entry"
  shows "degree_state t = degree_state s"
  using assms by (auto simp: meter_source_credit_def Let_def split: if_splits)

theorem metered_credit_consumes_the_actual_terminal_call_and_publication:
  fixes r :: execution_request
  defines "b \<equiv> request_binding r"
  assumes paid: "meter_source_credit policy ticket epoch index sequence route r s = (t, Credit_Metered entry)"
  defines "delivery \<equiv> Invoke_Protocol (binding_destination b) epoch index (Deliver_Intent route r)"
  shows "snd (core_result delivery (credit_core s)) = Protocol_Response (Delivery_Response (New_Credit b)) \<and>
    publish_at_sequence (binding_key b) sequence
      ((source_authority s)\<lparr>terminal_authority := finality_step delivery (credit_core s)\<rparr>) =
      (source_authority t, Primary_Published) \<and>
    exact_record_reference (credit_core s) index b Confirmed_Decision (request_certificate r) \<and>
    epoch = core_epoch (credit_core s)"
proof -
  let ?publish = "publish_at_sequence (binding_key b) sequence
    ((source_authority s)\<lparr>terminal_authority := finality_step delivery (credit_core s)\<rparr>)"
  have reply: "snd (core_result delivery (credit_core s)) = Protocol_Response (Delivery_Response (New_Credit b))"
    and actual: "fst ?publish = source_authority t" "snd ?publish = Primary_Published"
    using paid by (auto simp: meter_source_credit_def delivery_def Let_def b_def split: if_splits)
  have "?publish = (source_authority t, Primary_Published)" using actual by (cases ?publish) simp
  moreover have raw: "snd (invoke_protocol (binding_destination (request_binding r)) epoch index
      (Deliver_Intent route r) (credit_core s)) = Protocol_Response (Delivery_Response (New_Credit (request_binding r)))"
    using reply by (simp only: delivery_def b_def core_result.simps)
  moreover have "exact_record_reference (credit_core s) index b Confirmed_Decision (request_certificate r) \<and>
    epoch = core_epoch (credit_core s)"
    using actual_credit_response_consumes_confirmation[OF raw] by (simp only: b_def)
  ultimately show ?thesis using reply by blast
qed

theorem metered_credit_is_the_native_delivery_and_publication_word:
  assumes "meter_source_credit policy ticket epoch index sequence route r s = (t, Credit_Metered entry)"
  shows "credit_core t = run_finality
    [Invoke_Protocol (binding_destination (request_binding r)) epoch index (Deliver_Intent route r),
     Publish_Primary (binding_key (request_binding r))] (credit_core s)"
proof -
  let ?call = "Invoke_Protocol (binding_destination (request_binding r)) epoch index (Deliver_Intent route r)"
  let ?key = "binding_key (request_binding r)"
  have publication: "publish_at_sequence ?key sequence
      ((source_authority s)\<lparr>terminal_authority := finality_step ?call (credit_core s)\<rparr>) =
        (source_authority t, Primary_Published)"
    using metered_credit_consumes_the_actual_terminal_call_and_publication[OF assms] by blast
  show ?thesis
    using publication_at_sequence_uses_the_native_step[OF publication] by simp
qed

theorem metered_credit_projects_to_one_cutover_commit:
  fixes r :: execution_request
  defines "b \<equiv> request_binding r"
  assumes paid: "meter_source_credit policy ticket epoch index sequence route r s = (t, Credit_Metered entry)"
  shows "cutover_step policy grants (degree_state s)
      (Commit_Binding (prod_encode (binding_key b)) ticket (fst (binding_key b))
        (binding_destination b) (binding_amount b) True)
      (transition_result.Accepted Binding_Committed) (degree_state t) \<and>
    entry = billing_record (prod_encode (binding_key b)) (route_metadata (degree_state s))
      (transfer_commit b) \<and>
    billing_history (degree_state t) = billing_history (degree_state s) @ [entry]"
proof -
  let ?view = "degree_state s"
  let ?id = "prod_encode (binding_key b)"
  let ?action = "transfer_commit b"
  let ?flow = "fst (evaluate_flow policy (chosen_path ticket) True (binding_state ?view) ?action)"
  have eligible: "can_commit policy ?view ?id ticket ?action"
    and charge: "entry = billing_record ?id ticket ?action"
    and post: "degree_state t = ?view\<lparr>binding_state := ?flow,
      billing_history := billing_history ?view @ [entry]\<rparr>"
    using paid by (auto simp: meter_source_credit_def Let_def b_def split: if_splits)
  from eligible have matched: "ticket = route_metadata ?view"
    and legal: "legal_at policy (chosen_path ticket) ?action"
    by (auto simp: can_commit_def intro: order_trans)
  have step: "flow_step policy (chosen_path ticket) True (binding_state ?view) ?action
      (transition_result.Accepted (Committed_Value (binding_amount b))) ?flow"
    using legal by (simp add: flow_step_def)
  show ?thesis
    unfolding post
    using cutover_step.Commit[OF refl eligible step, of grants] charge matched by simp
qed

definition settle_expired_reservation ::
  "pending_resolution \<Rightarrow> lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
    reservation_machine \<Rightarrow> reservation_machine \<times> reservation_reply"
where
  "settle_expired_reservation mode c r duration m =
    (case reservation_at (machine_state m) (binding_key (request_binding r)) of
       None \<Rightarrow> (m, Request_Rejected)
     | Some res \<Rightarrow>
         let taken = reassign_worker c r duration m;
             generation = Suc (reservation_generation res);
             versions = asset_version (machine_state m)
         in if snd taken \<noteq> Worker_Reassigned then taken
            else case mode of
                Reconcile_Credit \<Rightarrow> reconcile_recorded_credit c r generation versions (fst taken)
              | Release_Reversal \<Rightarrow> release_to_source c r generation versions (fst taken))"

theorem settle_expired_reservation_releases_its_actual_lock:
  assumes consistent: "ownership_consistent (machine_state m)"
    and at: "reservation_at (machine_state m) (binding_key (request_binding r)) = Some res"
    and current: "current_use_allowed (lock_authority c) r"
    and duration: "duration > 0"
    and binding: "reservation_binding res = request_binding r"
    and pending: "reservation_phase res = Source_Pending"
    and expired: "reservation_deadline res \<le> reservation_clock (machine_state m)"
    and evidence: "case mode of
       Reconcile_Credit \<Rightarrow> request_binding r \<in> set (credit_history (received_messages (machine_state m)))
     | Release_Reversal \<Rightarrow> reversed_source_evidence (lock_authority c) r (machine_state m)"
  shows "snd (settle_expired_reservation mode c r duration m) = Reservation_Released \<and>
    (\<forall>asset. asset_owner (machine_state (fst (settle_expired_reservation mode c r duration m))) asset
      \<noteq> Some (binding_key (request_binding r)))"
  using evidence
proof (cases mode)
  case Reconcile_Credit
  then have credit: "request_binding r \<in> set (credit_history (received_messages (machine_state m)))"
    using evidence by simp
  show ?thesis
    using expired_pending_credit_recovers_in_two_calls[OF consistent at current duration binding pending expired credit]
    by (simp add: settle_expired_reservation_def Reconcile_Credit at Let_def)
next
  case Release_Reversal
  then have reversed: "reversed_source_evidence (lock_authority c) r (machine_state m)"
    using evidence by simp
  show ?thesis
    using expired_pending_reversal_recovers_in_two_calls[OF consistent at current duration binding pending expired reversed]
    by (simp add: settle_expired_reservation_def Release_Reversal at Let_def)
qed

end

end
