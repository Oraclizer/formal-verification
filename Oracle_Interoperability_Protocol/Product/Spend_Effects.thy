theory Spend_Effects
  imports Freeze_Interval
begin

record product_spend_authorization =
  spend_root :: transfer_binding
  spend_kind :: legal_action_kind
  spend_officer :: product_principal
  spend_sender :: product_principal
  spend_recipient :: product_principal
  spend_amount :: nat
  spend_jurisdiction :: nat
  spend_legal_basis :: nat
  spend_scope :: "product_asset set"
  spend_prior_seizure :: "source_key option"
  spend_appeal_deadline :: "nat option"

definition confiscation_spend_has_prior_seizure where
  "confiscation_spend_has_prior_seizure s authorization \<longleftrightarrow>
    (let root = spend_root authorization; asset = binding_asset root in
      (legal_current_state s (binding_destination root) asset \<in> {Some SEIZED, Some CONFISCATED}) \<and>
      (\<exists>key event deadline. active_seizure_event s asset = Some key \<and>
        spend_prior_seizure authorization = Some key \<and> committed_legal_events s key = Some event \<and>
        legal_asset (applied_order event) = asset \<and> legal_action (applied_order event) = SEIZE \<and>
        spend_appeal_deadline authorization = Some deadline \<and>
        recorded_appeal_deadline s asset = Some deadline \<and> deadline \<le> legal_clock s))"

lemma confiscation_spend_checks_the_recorded_appeal_deadline:
  assumes "confiscation_spend_has_prior_seizure s authorization"
  shows "\<exists>deadline. spend_appeal_deadline authorization = Some deadline \<and>
    recorded_appeal_deadline s (binding_asset (spend_root authorization)) = Some deadline \<and>
    deadline \<le> legal_clock s"
  using assms by (auto simp: confiscation_spend_has_prior_seizure_def Let_def)

definition exact_spend_authorization where
  "exact_spend_authorization grant spend_verified who payload r root sender recipient amount kind authorization s \<longleftrightarrow>
    spend_verified who payload authorization \<and> spend_officer authorization = who \<and>
    spend_root authorization = root \<and> spend_kind authorization = kind \<and>
    spend_sender authorization = sender \<and> spend_recipient authorization = recipient \<and>
    spend_amount authorization = amount \<and> spend_legal_basis authorization \<noteq> 0 \<and>
    binding_asset root \<in> spend_scope authorization \<and> request_caller r = who \<and>
    grant who (spend_jurisdiction authorization) (binding_asset root) kind (cut_authority_epoch (legal_current_cut s)) \<and>
    enforcement_transfer_action kind \<and>
    (kind = Legal_Confiscate \<longrightarrow> confiscation_spend_has_prior_seizure s authorization)"

definition governed_spend_is_admitted where
  "governed_spend_is_admitted grant spend_verified who payload authorization s \<longleftrightarrow>
    (case envelope_command (payload_envelope payload) of
       Client_Protocol endpoint index (Descendant_Intent r root sender recipient amount) \<Rightarrow>
         (case binding_operation (request_binding r) of Ordinary_Transfer_Effect \<Rightarrow> authorization = None
          | Enforcement_Transfer_Effect kind \<Rightarrow> (case authorization of None \<Rightarrow> False
              | Some order \<Rightarrow> exact_spend_authorization grant spend_verified who payload r root sender recipient amount kind order s)
          | _ \<Rightarrow> False)
     | _ \<Rightarrow> False)"

datatype governed_spend_reply = Spend_Blocked | Spend_Checked checked_execution_reply

record governed_spend_receipt =
  spend_receipt_payload :: product_call_payload
  spend_receipt_order :: "product_spend_authorization option"
  spend_receipt_reply :: governed_spend_reply

record regulated_product_world =
  regulated_orders :: governed_world
  spend_receipts :: "client_call_id \<Rightarrow> governed_spend_receipt option"

definition initial_regulated_product where
  "initial_regulated_product s = \<lparr>regulated_orders = initial_governed_world s, spend_receipts = (\<lambda>_. None)\<rparr>"

definition regulated_read_world where
  "regulated_read_world s = legal_reads (governed_legal (regulated_orders s))"

definition replace_regulated_reads where
  "replace_regulated_reads reads s = s\<lparr>regulated_orders := (regulated_orders s)\<lparr>governed_legal :=
    (governed_legal (regulated_orders s))\<lparr>legal_reads := reads\<rparr>\<rparr>\<rparr>"

context source_attestation
begin

definition run_spend_effect where
  "run_spend_effect grant spend_verified permitted verified maintainers registered verified_ack
      entry who expected call_id payload authorization s =
    (let legal = governed_legal (regulated_orders s); reads = legal_reads legal in
      if \<not> read_authority_available reads then (s, Spend_Checked Checked_Execution_Unavailable)
      else if governed_spend_is_admitted grant spend_verified who payload authorization legal then
        let step = execute_at_checked_cut permitted verified maintainers registered verified_ack
          (regulatory_lock_entry entry) who expected call_id payload reads
        in (replace_regulated_reads (fst step) s, Spend_Checked (snd step))
      else (s, Spend_Blocked))"

lemma blocked_spend_effect_leaves_the_world_unchanged:
  assumes "snd (run_spend_effect grant spend_verified permitted verified maintainers registered verified_ack
       entry who expected call_id payload authorization s) = Spend_Blocked"
  shows "fst (run_spend_effect grant spend_verified permitted verified maintainers registered verified_ack
       entry who expected call_id payload authorization s) = s"
  using assms by (simp add: run_spend_effect_def Let_def split: if_splits)

end

end
