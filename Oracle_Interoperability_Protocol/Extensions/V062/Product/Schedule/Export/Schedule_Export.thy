theory Schedule_Export
  imports "OIP_Schedule_Cases.Schedule_Cases" "HOL-Library.Code_Target_Nat"
begin

lemma sc_compatible_code [code]:
  "sp_compatible se_first se_second =
    (case se_first of SP_Serial_Class \<Rightarrow> False
     | SP_Observation_Class se_origin se_publication \<Rightarrow> se_second \<noteq> SP_Serial_Class
     | SP_Slot_Class se_key se_publication \<Rightarrow>
         (case se_second of SP_Serial_Class \<Rightarrow> False
          | SP_Observation_Class se_other_origin se_other_publication \<Rightarrow> True
          | SP_Slot_Class se_other_key se_other_publication \<Rightarrow> se_key \<noteq> se_other_key))"
  by (cases se_first; cases se_second)
    (auto simp: sp_shared_authority_writer_is_always_serial
      sp_slot_compatibility_is_exact_full_key_inequality sp_observation_and_queue_slot_are_compatible
      sp_compatible_def Let_def split: option.splits)

definition sc_bit :: "bool \<Rightarrow> nat" where "sc_bit se_value = (if se_value then 1 else 0)"

definition sc_key_words where
  "sc_key_words se_key = (case se_key of ((se_domain,se_event),se_epoch_id,se_position) \<Rightarrow> [se_domain,se_event,se_epoch_id,se_position])"

definition sc_binding_words where
  "sc_binding_words se_binding = [fst (ss_origin se_binding),snd (ss_origin se_binding),ss_asset se_binding,ss_owner se_binding,
    ss_destination se_binding,ss_recipient se_binding,ss_amount se_binding]"

fun sc_status_word where
  "sc_status_word Secondary_Waiting = (0::nat)"
| "sc_status_word Secondary_In_Flight = 1"
| "sc_status_word Secondary_Completed = 2"

definition sc_publication_words where
  "sc_publication_words se_pub =
    (let se_decision = publication_decision (sp_publication_model se_pub); se_binding = origin_binding se_decision in
      sc_key_words (sp_key_of se_pub) @ [sp_publication_owner se_pub,binding_asset se_binding,binding_amount se_binding,
        binding_destination se_binding,binding_recipient se_binding,origin_epoch se_decision,
        (if origin_kind se_decision = Confirmed_Decision then 1 else 2)])"

definition sc_job_words where
  "sc_job_words se_job = [sp_job_target se_job,sp_job_attempts se_job,sc_status_word (sp_job_status se_job)] @
    sc_publication_words (sp_job_publication se_job)"

fun sc_reply_words where
  "sc_reply_words (SP_Queue_Result (SP_Enqueued None)) = [0,0,0]"
| "sc_reply_words (SP_Queue_Result (SP_Enqueued (Some se_key))) = [0,0,1] @ sc_key_words se_key"
| "sc_reply_words (SP_Queue_Result (SP_Dispatched None)) = [0,1,0]"
| "sc_reply_words (SP_Queue_Result (SP_Dispatched (Some se_job))) = [0,1,1] @ sc_job_words se_job"
| "sc_reply_words (SP_Queue_Result (SP_Changed se_value)) = [0,2,sc_bit se_value]"
| "sc_reply_words (SP_Other_Result (SS_Executed se_code None)) = [1,0,se_code,0,0,0]"
| "sc_reply_words (SP_Other_Result (SS_Executed se_code (Some (se_epoch_id,se_position)))) = [1,0,se_code,1,se_epoch_id,se_position]"
| "sc_reply_words (SP_Other_Result (SS_Raw_Value se_value)) = [1,1,se_value]"
| "sc_reply_words (SP_Other_Result (SS_Current_Value None)) = [1,2,0,0,0,0]"
| "sc_reply_words (SP_Other_Result (SS_Current_Value (Some (se_observed_cut,se_value)))) =
    [1,2,1,cut_authority_epoch se_observed_cut,cut_revision se_observed_cut,se_value]"
| "sc_reply_words (SP_Other_Result (SS_Historical_Value None)) = [1,3,0,0,0]"
| "sc_reply_words (SP_Other_Result (SS_Historical_Value (Some (se_position,se_value)))) = [1,3,1,se_position,se_value]"
| "sc_reply_words (SP_Other_Result (SS_Changed se_value)) = [1,4,sc_bit se_value]"
| "sc_reply_words (SP_Other_Result SS_Endpoint_Rejected) = [1,5]"
| "sc_reply_words (SP_Other_Result SS_Unsupported) = [1,6]"
| "sc_reply_words SP_Maintenance_Refused = [2]"

fun sc_supported_reply where
  "sc_supported_reply (SP_Other_Result SS_Unsupported) = False"
| "sc_supported_reply se_reply = True"

definition sc_snapshot_rows where
  "sc_snapshot_rows se_role se_prefix_index se_snapshot =
    map (\<lambda>(se_asset,se_value). [23,se_role,se_prefix_index,se_asset,se_value]) (ss_values se_snapshot) @
    map (\<lambda>(se_asset,se_value). [24,se_role,se_prefix_index,se_asset,se_value]) (ss_versions se_snapshot) @
    map (\<lambda>((se_domain,se_asset,se_holder),se_value). [25,se_role,se_prefix_index,se_domain,se_asset,se_holder,se_value]) (ss_balances se_snapshot)"

definition sc_state_rows where
  "sc_state_rows se_role se_state =
    (let se_data = sp_data se_state; se_snapshot = ss_current se_data in
      [[10,se_role,ss_epoch se_data,ss_revision se_data,ss_clock se_data,ss_provider se_data,
        sc_bit (ss_connected se_data),sc_bit (ss_current_allowed se_data),sp_target se_state]] @
      map (\<lambda>(se_asset,se_value). [11,se_role,se_asset,se_value]) (ss_values se_snapshot) @
      map (\<lambda>(se_asset,se_value). [12,se_role,se_asset,se_value]) (ss_versions se_snapshot) @
      map (\<lambda>((se_domain,se_asset,se_holder),se_value). [13,se_role,se_domain,se_asset,se_holder,se_value]) (ss_balances se_snapshot) @
      map (\<lambda>(se_key,se_slot). [14,se_role,fst se_key,snd se_key] @ sc_binding_words (ss_reserved_binding se_slot) @
        [ss_generation se_slot,ss_holder se_slot,ss_deadline se_slot,ss_phase se_slot,sc_bit (ss_terminal se_slot \<noteq> None),
         (case ss_terminal se_slot of None \<Rightarrow> 0 | Some se_reference \<Rightarrow> se_reference)]) (ss_reservations se_data) @
      map (\<lambda>(se_asset,se_key). [15,se_role,se_asset,fst se_key,snd se_key]) (ss_active se_data) @
      map (\<lambda>(se_reference,se_binding). [16,se_role,se_reference] @ sc_binding_words se_binding) (ss_evidence se_data) @
      map (\<lambda>(se_key,se_pub). [17,se_role,fst se_key,snd se_key] @ sc_publication_words se_pub) (ss_decisions se_data) @
      map (\<lambda>(se_key,se_pub). [18,se_role,fst se_key,snd se_key] @ sc_publication_words se_pub) (sp_publications se_state) @
      map (\<lambda>((se_key,(se_domain,se_asset,se_holder)),se_value). [19,se_role,fst se_key,snd se_key,se_domain,se_asset,se_holder,se_value]) (ss_funding se_data) @
      concat (map (\<lambda>se_key. case sp_jobs se_state se_key of None \<Rightarrow> []
         | Some se_job \<Rightarrow> [[20,se_role] @ sc_key_words se_key @ sc_job_words se_job]) (sp_known_keys se_state)) @
      map (\<lambda>((se_namespace,se_sequence),(se_request,se_reply)). [21,se_role,se_namespace,se_sequence] @
         sc_reply_words (SP_Other_Result se_reply)) (ss_calls se_data) @
      concat (map (\<lambda>(se_prefix_index,se_entry). sc_snapshot_rows se_role se_prefix_index se_entry)
        (zip [0..<length (ss_prefixes se_data)] (ss_prefixes se_data))))"

definition sc_decode_kind where
  "sc_decode_kind se_word = (if se_word = 0 then Some SC_Enqueue else if se_word = 1 then Some SC_Dispatch
     else if se_word = 2 then Some SC_Fail else None)"

definition sc_decode where
  "sc_decode se_words = (case se_words of [] \<Rightarrow> None | se_tag # se_fields \<Rightarrow>
    if se_tag = 0 then (case se_fields of [se_a,se_b,se_oa,se_ob,se_ca,se_cb,se_requested] \<Rightarrow>
       if se_requested > 1 then None else (case (sc_decode_kind se_a,sc_decode_kind se_b) of
          (Some se_first_kind,Some se_second_kind) \<Rightarrow> Some (SC_Queue_Pair se_first_kind se_second_kind se_oa se_ob se_ca se_cb (se_requested = 1))
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)
    else if se_tag = 1 then (case se_fields of [se_event,se_epoch_id,se_domain,se_asset,se_recipient,se_amount,se_requested] \<Rightarrow>
       if se_requested > 1 then None else Some (SC_Read_Queue se_event se_epoch_id se_domain se_asset se_recipient se_amount (se_requested = 1)) | _ \<Rightarrow> None)
    else if se_tag = 2 then (case se_fields of [se_a,se_b,se_epoch_id,se_requested] \<Rightarrow>
       if se_requested > 1 then None else Some (SC_Shared_Cut se_a se_b se_epoch_id (se_requested = 1)) | _ \<Rightarrow> None)
    else if se_tag = 3 then (case se_fields of [se_asset,se_old_revision,se_new_revision,se_old_value,se_new_value,se_requested] \<Rightarrow>
       if se_requested > 1 then None else Some (SC_Current_Read se_asset se_old_revision se_new_revision se_old_value se_new_value (se_requested = 1)) | _ \<Rightarrow> None)
    else if se_tag = 4 then (case se_fields of [se_old_epoch,se_new_epoch,se_asset,se_revision,se_requested] \<Rightarrow>
       if se_requested > 1 then None else Some (SC_Policy se_old_epoch se_new_epoch se_asset se_revision (se_requested = 1)) | _ \<Rightarrow> None)
    else if se_tag = 5 then (case se_fields of [se_oa,se_ob,se_requested] \<Rightarrow>
       if se_requested > 1 then None else Some (SC_Publish se_oa se_ob (se_requested = 1)) | _ \<Rightarrow> None)
    else if se_tag = 6 then (case se_fields of [se_actor,se_namespace,se_sequence,se_requested] \<Rightarrow>
       if se_requested > 1 then None else Some (SC_Namespace se_actor se_namespace se_sequence (se_requested = 1)) | _ \<Rightarrow> None)
    else if se_tag = 7 then (case se_fields of [se_a,se_b,se_c,se_oa,se_ob] \<Rightarrow> Some (SC_Finite se_a se_b se_c se_oa se_ob) | _ \<Rightarrow> None)
    else if se_tag = 8 then (case se_fields of [se_event,se_attempts] \<Rightarrow> Some (SC_Bounded se_event se_attempts) | _ \<Rightarrow> None)
    else None)"

definition sc_observe where
  "sc_observe se_mode se_input_words se_prepared =
    (case sc_execute (se_mode \<noteq> 2) (se_mode \<noteq> 0) se_prepared of None \<Rightarrow> [[0,1,se_mode,3]]
     | Some (se_final,se_order,se_choices,se_replies) \<Rightarrow>
       let se_prior_probes = sc_probes (sc_before_probes se_prepared) (sc_seed se_prepared);
           se_later_probes = sc_probes (sc_after_probes se_prepared) se_final in
       if \<not> list_all (\<lambda>se_entry. case se_entry of None \<Rightarrow> False | Some (se_label,se_reply) \<Rightarrow> sc_supported_reply se_reply) se_replies \<or>
          \<not> list_all sc_supported_reply (se_prior_probes @ se_later_probes)
       then [[0,1,se_mode,4]]
       else [[0,1,se_mode,0],[1] @ se_input_words,[2] @ sc_adjacent se_prepared,[3] @ se_order,[4] @ map sc_bit se_choices] @
         concat (map (\<lambda>(se_index,se_entry). case se_entry of None \<Rightarrow> []
            | Some (se_label,se_reply) \<Rightarrow> [[5,se_index,se_label] @ sc_reply_words se_reply]) (zip [0..<length se_replies] se_replies)) @
         map (\<lambda>(se_index,se_reply). [6,se_index] @ sc_reply_words se_reply) (zip [0..<length se_prior_probes] se_prior_probes) @
         map (\<lambda>(se_index,se_reply). [7,se_index] @ sc_reply_words se_reply) (zip [0..<length se_later_probes] se_later_probes) @
         sc_state_rows 0 (sc_seed se_prepared) @ sc_state_rows 1 se_final)"

definition sc_abi where
  "sc_abi se_mode se_words = (if se_mode > 2 \<or> \<not> list_all (\<lambda>se_word. se_word < 2^64) se_words then [[0,1,se_mode,1]]
    else case sc_decode se_words of None \<Rightarrow> [[0,1,se_mode,1]]
    | Some se_input \<Rightarrow> case sc_prepare se_input of None \<Rightarrow> [[0,1,se_mode,2]]
      | Some se_prepared \<Rightarrow> sc_observe se_mode se_words se_prepared)"

definition sc_integer_abi :: "integer \<Rightarrow> integer list \<Rightarrow> integer list list" where
  "sc_integer_abi se_mode se_words = (if se_mode < 0 \<or> list_ex (\<lambda>se_word. se_word < 0) se_words
    then [[0,1,se_mode,1]] else map (map integer_of_nat) (sc_abi (nat_of_integer se_mode) (map nat_of_integer se_words)))"

lemma sc_decode_failure_has_no_protocol_verdict:
  assumes "sc_decode se_words = None"
  shows "sc_abi se_mode se_words = [[0,1,se_mode,1]]"
  using assms by (simp add: sc_abi_def)

lemma sc_missing_seed_has_no_protocol_verdict:
  assumes "se_mode \<le> 2" "list_all (\<lambda>se_word. se_word < 2^64) se_words"
    "sc_decode se_words = Some se_input" "sc_prepare se_input = None"
  shows "sc_abi se_mode se_words = [[0,1,se_mode,2]]"
  using assms by (simp add: sc_abi_def)

text \<open>
  Output rows are an observation ABI, not an input oracle. Metadata statuses
  are 1 malformed/out-of-domain input, 2 unestablished operational seed,
  3 invalid plan and 4 unmodeled branch/missing occurrence. These return no
  protocol verdict. Integer input is lossless and checked before nat conversion.
  Row 0 status 0 allows the result rows; every result is computed by the closed
  operations. The finite map projection observes every key introduced by this
  empty-queue fixture and its operations. It does not claim serialized retained
  image equality, raw journal equality or a signed transport release result.
\<close>

code_reserved (SML) before

export_code sc_integer_abi in SML module_name OIP_Schedule file_prefix "oip_schedule"

end
