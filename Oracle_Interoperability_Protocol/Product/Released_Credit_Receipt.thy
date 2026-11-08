theory Released_Credit_Receipt
  imports Durable_Call_Completion
begin

fun exact_applied_credit ::
  "transfer_binding \<Rightarrow> (client_command, finality_reply, nat \<times> lock_context) authority_call_entry \<Rightarrow> bool" where
  "exact_applied_credit binding (Authority_Executed call_id (Client_Protocol endpoint index (Deliver_Intent route request))
    (Protocol_Response (Delivery_Response (New_Credit applied)))) =
      (request_binding request = binding \<and> applied = binding)"
| "exact_applied_credit binding entry = False"

definition original_credit_authority_position where
  "original_credit_authority_position binding log =
    map_option fst (List.find (\<lambda>(_, entry). exact_applied_credit binding entry) (enumerate 0 log))"

lemma credit_position_names_an_exact_applied_entry:
  assumes found: "original_credit_authority_position binding log = Some position"
  shows "position < length log \<and> exact_applied_credit binding (log ! position)"
proof -
  let ?predicate = "\<lambda>(_, entry). exact_applied_credit binding entry"
  obtain entry where hit: "List.find ?predicate (enumerate 0 log) = Some (position, entry)"
    using found unfolding original_credit_authority_position_def by (cases "List.find ?predicate (enumerate 0 log)") auto
  have witness: "\<exists>i<length (enumerate 0 log).
      ?predicate (enumerate 0 log ! i) \<and>
      (position, entry) = enumerate 0 log ! i \<and>
      (\<forall>j<i. \<not> ?predicate (enumerate 0 log ! j))"
    by (rule find_Some_iff[THEN iffD1, OF hit])
  from witness show ?thesis by (auto simp: nth_enumerate_eq)
qed

lemma original_credit_position_cannot_be_replaced_by_an_appended_result:
  assumes "original_credit_authority_position binding log = Some position"
  shows "original_credit_authority_position binding (log @ later) = Some position"
proof -
  have keep: "List.find p (prior @ suffix) = List.find p prior" if "List.find p prior \<noteq> None" for p prior suffix
    using that by (induction prior) (auto split: if_splits)
  have "List.find (\<lambda>(_, entry). exact_applied_credit binding entry) (enumerate 0 log) \<noteq> None"
    using assms by (auto simp: original_credit_authority_position_def)
  then show ?thesis using assms
    by (simp add: original_credit_authority_position_def enumerate_append_eq keep)
qed

lemma reopened_credit_position_uses_the_retained_log:
  "original_credit_authority_position binding
     (call_authority_log (product_calls (reopen_retained_source connection records))) =
   original_credit_authority_position binding (retained_log records)"
  by (simp add: reopen_retained_source_def)

lemma a_duplicate_reply_cannot_supply_the_original_credit_position:
  "original_credit_authority_position binding
    [Authority_Executed duplicate (Client_Protocol endpoint index (Deliver_Intent route request))
      (Protocol_Response (Delivery_Response (Duplicate_Credit applied)))] = None"
  by (simp add: original_credit_authority_position_def)


definition released_credit_credential where
  "released_credit_credential who binding supplied source \<longleftrightarrow>
    (let rs = authoritative_reservation_state source;
         key = binding_key binding; asset = binding_asset binding
     in asset_owner rs asset \<noteq> Some key \<and>
       (case (supplied, reservation_at rs key) of (Some credential, Some reservation) \<Rightarrow>
          reservation_binding reservation = binding \<and>
          reservation_worker reservation = who \<and>
          credential_origin credential = key \<and>
          credential_epoch credential = cut_authority_epoch (current_product_cut source) \<and>
          credential_token credential =
            \<lparr>token_asset = asset, token_owner = who, token_generation = reservation_generation reservation\<rparr>
        | _ \<Rightarrow> False))"

definition released_credit_reference where
  "released_credit_reference permitted verified registered entry who call_id payload s =
    (let outcomes = origin_outcomes s; source = outcome_source outcomes; envelope = payload_envelope payload;
         calls = product_calls source
     in case envelope_command envelope of Client_Protocol endpoint index (Deliver_Intent route request) \<Rightarrow>
         let binding = request_binding request
         in if outcome_entries outcomes call_id = None \<and> product_new_call who call_id envelope source \<and>
               result_access_bound verified who call_id payload outcomes \<and>
               permitted entry who (envelope_command envelope) \<and> registered_lock_envelope registered envelope \<and>
               command_binding_matches envelope (envelope_command envelope) \<and>
               existing_decision_matches s binding Confirmed_Decision (payload_origin_epoch payload) \<and>
               terminal_intent_guard (call_authority_state calls) index (Deliver_Intent route request) \<and>
               released_credit_credential who binding (payload_credential payload) source
            then map_option (Pair binding) (original_credit_authority_position binding (call_authority_log calls))
            else None
      | _ \<Rightarrow> None)"

definition record_released_credit_receipt where
  "record_released_credit_receipt permitted verified registered entry who call_id payload s =
    (case released_credit_reference permitted verified registered entry who call_id payload s of None \<Rightarrow> (s, None)
     | Some (binding, position) \<Rightarrow>
       let outcomes = origin_outcomes s;
           reply = Authority_Reply (Protocol_Response (Delivery_Response (Duplicate_Credit binding)))
       in (s\<lparr>origin_outcomes := store_product_result call_id payload reply (outcome_source outcomes) outcomes\<rparr>,
           Some position))"

lemma released_credit_receipt_selects_an_exact_prior_credit:
  assumes "released_credit_reference permitted verified registered entry who call_id payload s = Some (binding, position)"
  defines "log \<equiv> call_authority_log (product_calls (outcome_source (origin_outcomes s)))"
  shows "position < length log \<and> exact_applied_credit binding (log ! position)"
proof -
  have "original_credit_authority_position binding log = Some position"
    using assms(1) unfolding log_def
    by (auto simp: released_credit_reference_def Let_def
        split: client_command.splits protocol_intent.splits option.splits if_splits)
  then show ?thesis by (rule credit_position_names_an_exact_applied_entry)
qed

lemma released_credit_receipt_preserves_authority_and_old_results:
  assumes selected: "released_credit_reference permitted verified registered entry who call_id payload s = Some (binding, position)"
  defines "after \<equiv> fst (record_released_credit_receipt permitted verified registered entry who call_id payload s)"
  shows "snd (record_released_credit_receipt permitted verified registered entry who call_id payload s) = Some position"
    "outcome_source (origin_outcomes after) = outcome_source (origin_outcomes s)"
    "origin_decisions after = origin_decisions s"
    "origin_debits after = origin_debits s"
    "outcome_completed (origin_outcomes after) = outcome_completed (origin_outcomes s)"
    "outcome_entries (origin_outcomes after) call_id =
      Some \<lparr>result_payload = payload, result_outcome =
        Authority_Reply (Protocol_Response (Delivery_Response (Duplicate_Credit binding)))\<rparr>"
    "other_id \<noteq> call_id \<Longrightarrow>
      outcome_entries (origin_outcomes after) other_id = outcome_entries (origin_outcomes s) other_id"
  using selected by (simp_all add: after_def record_released_credit_receipt_def store_product_result_def Let_def)

lemma an_unselected_call_cannot_record_a_released_credit_receipt:
  assumes "released_credit_reference permitted verified registered entry who call_id payload s = None"
  shows "record_released_credit_receipt permitted verified registered entry who call_id payload s = (s, None)"
  using assms by (simp add: record_released_credit_receipt_def)

lemma a_released_credit_receipt_requires_the_current_credential_epoch:
  assumes "released_credit_credential who binding (Some credential) source"
  shows "credential_epoch credential = cut_authority_epoch (current_product_cut source)"
  using assms by (simp add: released_credit_credential_def Let_def split: option.splits)

lemma the_released_credit_path_does_not_take_a_fresh_refund:
  assumes "envelope_command (payload_envelope payload) =
    Client_Protocol endpoint index (Return_Intent request generation versions)"
  shows "record_released_credit_receipt permitted verified registered entry who call_id payload s = (s, None)"
  using assms by (simp add: record_released_credit_receipt_def released_credit_reference_def Let_def)


lemma released_credit_result_keeps_the_underlying_source:
  assumes "snd (record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload
    (settlement_primary (read_authority (regulated_read_world s)))) \<noteq> None"
  shows "outcome_source (current_product_outcomes (replace_product_outcomes (origin_outcomes
    (fst (record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload
      (settlement_primary (read_authority (regulated_read_world s)))))) s)) = outcome_source (current_product_outcomes s)"
proof -
  let ?origins = "settlement_primary (read_authority (regulated_read_world s))"
  let ?result = "record_released_credit_receipt permitted verified registered Normal_Lock_Entry actor call_id payload ?origins"
  obtain binding position where reference:
    "released_credit_reference permitted verified registered Normal_Lock_Entry actor call_id payload ?origins =
      Some (binding, position)"
    using assms
    by (cases "released_credit_reference permitted verified registered Normal_Lock_Entry actor call_id payload ?origins")
      (auto simp: record_released_credit_receipt_def split: prod.splits)
  have authority: "outcome_source (origin_outcomes (fst ?result)) = outcome_source (origin_outcomes ?origins)"
    by (rule released_credit_receipt_preserves_authority_and_old_results(2)[OF reference])
  have current: "origin_outcomes ?origins = current_product_outcomes s"
    by (simp add: current_product_outcomes_def legal_underlying_outcomes_def regulated_read_world_def)
  show ?thesis by (simp only: replacement_supplies_exact_outcome_table authority current)
qed

end
