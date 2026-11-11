theory Receiver_State_Branches
  imports "OIP_Settlement_Queue_G0.Settlement_Queue_G0"
    "OIP_Message_Code.Wire_Code_Session_Claim_Bytes"
    "OIP_Source_Writer_JSON_G0.Source_Writer_JSON_G0"
begin

type_synonym rr_control = "nat \<times> wire_bytes"

record rr_state =
  rr_profile :: sw_json_profile
  rr_target :: nat
  rr_receipts :: "sq_publication list"

definition rr_origin_json where
  "rr_origin_json origin =
    code_json_open_key ''domain'' @ sw_decimal (fst origin) @
    code_json_next_key ''event'' @ sw_decimal (snd origin) @ [125]"

definition rr_publication_json where
  "rr_publication_json published =
    (let pub = fst published; decision = publication_decision pub; binding = origin_binding decision
     in code_json_open_key ''origin'' @ rr_origin_json (publication_origin pub) @
       code_json_next_key ''decision'' @ code_json_open_key ''binding'' @
       code_json_open_key ''origin'' @ rr_origin_json (binding_key binding) @
       code_json_next_key ''asset'' @ sw_decimal (binding_asset binding) @
       code_json_next_key ''owner'' @ sw_decimal (snd published) @
       code_json_next_key ''destination'' @ sw_decimal (binding_destination binding) @
       code_json_next_key ''recipient'' @ sw_decimal (binding_recipient binding) @
       code_json_next_key ''amount'' @ sw_decimal (binding_amount binding) @ [125] @
       code_json_next_key ''kind'' @ [34] @
       code_json_ascii (if origin_kind decision = Confirmed_Decision then ''Confirmed'' else ''Reversed'') @ [34] @
       code_json_next_key ''origin_epoch'' @ sw_decimal (origin_epoch decision) @
       code_json_next_key ''commit'' @ code_json_open_key ''position'' @
       sw_decimal (origin_commit_position decision) @ [125,125,125])"

definition rr_state_json where
  "rr_state_json state =
    code_json_open_key ''profile'' @ sw_profile_json (rr_profile state) @
    code_json_next_key ''target'' @ sw_decimal (rr_target state) @
    code_json_next_key ''receipts'' @ sw_json_array (map rr_publication_json (rr_receipts state)) @ [125]"

definition rr_parse_origin where
  "rr_parse_origin bytes =
    Option.bind (code_json_first_field ''domain'' code_json_u64 bytes) (\<lambda>(domain,after_domain).
      Option.bind (code_json_next_field ''event'' code_json_u64 after_domain) (\<lambda>(event,after_event).
        map_option (Pair (domain,event)) (code_json_expect [125] after_event)))"

fun rr_parse_number_fields where
  "rr_parse_number_fields [] bytes = Some ([],bytes)"
| "rr_parse_number_fields (name # names) bytes =
    Option.bind (code_json_next_field name code_json_u64 bytes) (\<lambda>(number,rest).
      map_option (\<lambda>(numbers,tail). (number # numbers,tail)) (rr_parse_number_fields names rest))"

definition rr_parse_binding where
  "rr_parse_binding bytes =
    Option.bind (code_json_first_field ''origin'' rr_parse_origin bytes) (\<lambda>(origin,after_origin).
      Option.bind (rr_parse_number_fields [''asset'',''owner'',''destination'',''recipient'',''amount''] after_origin)
        (\<lambda>(fields,after_fields). map_option (Pair (origin,fields)) (code_json_expect [125] after_fields)))"

definition rr_parse_commit where
  "rr_parse_commit bytes =
    Option.bind (code_json_first_field ''position'' code_json_u64 bytes) (\<lambda>(position,after_position).
      map_option (Pair position) (code_json_expect [125] after_position))"

definition rr_parse_decision where
  "rr_parse_decision bytes =
    Option.bind (code_json_first_field ''binding'' rr_parse_binding bytes) (\<lambda>((origin,fields),after_binding).
      Option.bind (code_json_next_field ''kind'' (code_json_enum [''Confirmed'',''Reversed'']) after_binding)
        (\<lambda>(kind,after_kind).
          Option.bind (code_json_next_field ''origin_epoch'' code_json_u64 after_kind) (\<lambda>(epoch,after_epoch).
            Option.bind (code_json_next_field ''commit'' rr_parse_commit after_epoch) (\<lambda>(position,after_commit).
              map_option (Pair ([position] @ fields @ [epoch,Suc kind,fst origin,snd origin]))
                (code_json_expect [125] after_commit)))))"

definition rr_set_binding_origin where
  "rr_set_binding_origin origin published =
    (let pub = fst published; decision = publication_decision pub in
     (pub\<lparr>publication_decision := decision\<lparr>origin_binding := (origin_binding decision)\<lparr>binding_key := origin\<rparr>\<rparr>\<rparr>,
       snd published))"

fun rr_publication_from_words :: "nat list \<Rightarrow> sq_publication option" where
  "rr_publication_from_words [domain,event,position,asset,owner,destination,recipient,amount,epoch,kind,binding_domain,binding_event] =
    map_option (rr_set_binding_origin (binding_domain,binding_event))
      (sq_parse_publication [domain,event,position,asset,owner,destination,recipient,amount,epoch,kind])"
| "rr_publication_from_words _ = None"

definition rr_parse_publication where
  "rr_parse_publication bytes =
    Option.bind (code_json_first_field ''origin'' rr_parse_origin bytes) (\<lambda>((domain,event),after_origin).
      Option.bind (code_json_next_field ''decision'' rr_parse_decision after_origin) (\<lambda>(fields,after_decision).
        Option.bind (rr_publication_from_words (domain # event # fields)) (\<lambda>published.
          map_option (Pair published) (code_json_expect [125] after_decision))))"

definition rr_parse_state where
  "rr_parse_state bytes =
    Option.bind (code_json_first_field ''profile'' code_json_source_profile bytes) (\<lambda>(profile,after_profile).
      Option.bind (code_json_next_field ''target'' code_json_u64 after_profile) (\<lambda>(target,after_target).
        Option.bind (code_json_next_field ''receipts'' (code_json_array rr_parse_publication) after_target)
          (\<lambda>(receipts,after_receipts).
            map_option (Pair \<lparr>rr_profile = profile, rr_target = target, rr_receipts = receipts\<rparr>)
              (code_json_expect [125] after_receipts))))"

definition rr_publication_origin_matches where
  "rr_publication_origin_matches published \<longleftrightarrow>
    publication_origin (fst published) = binding_key (origin_binding (publication_decision (fst published)))"

definition rr_read where
  "rr_read profile target bytes =
    (if bytes = [] then Some \<lparr>rr_profile = profile,rr_target = target,rr_receipts = []\<rparr>
     else Option.bind (code_json_complete rr_parse_state bytes) (\<lambda>state.
       if rr_state_json state = bytes \<and> rr_profile state = profile \<and> rr_target state = target \<and>
         sq_sorted_keys (map sq_key (rr_receipts state)) \<and> list_all rr_publication_origin_matches (rr_receipts state)
       then Some state else None))"

definition rr_find where
  "rr_find key state = List.find (\<lambda>published. sq_key published = key) (rr_receipts state)"

fun rr_insert where
  "rr_insert published [] = [published]"
| "rr_insert published (old # rest) =
    (if sq_key_less (sq_key published) (sq_key old) then published # old # rest
     else old # rr_insert published rest)"

definition rr_allowed where
  "rr_allowed profile target dispatch_profile job \<longleftrightarrow>
    dispatch_profile = profile \<and> sq_job_target job = target \<and>
    sq_phase job = Secondary_In_Flight \<and> sq_attempts job > 0 \<and>
    rr_publication_origin_matches (sq_commitment job)"

datatype rr_plan = RR_Refused | RR_Already_Recorded | RR_Compare rr_control wire_bytes

definition rr_prepare where
  "rr_prepare profile target dispatch_profile job prior_value =
    (if \<not> rr_allowed profile target dispatch_profile job then RR_Refused
     else case rr_read profile target (snd prior_value) of None \<Rightarrow> RR_Refused
     | Some state \<Rightarrow> let published = sq_commitment job in
       case rr_find (sq_key published) state of Some old \<Rightarrow>
         if old = published then RR_Already_Recorded else RR_Refused
       | None \<Rightarrow> RR_Compare prior_value (rr_state_json (state\<lparr>rr_receipts := rr_insert published (rr_receipts state)\<rparr>)))"

datatype rr_replace = RR_Installed | RR_Compare_Failed | RR_Ambiguous
datatype rr_result = RR_Error | RR_Exact | RR_Changed

definition rr_readback where
  "rr_readback profile target key raw =
    Option.bind (rr_read profile target raw) (rr_find key)"

definition rr_finish where
  "rr_finish profile target job replacement reread =
    (case replacement of RR_Installed \<Rightarrow> RR_Changed
     | _ \<Rightarrow>
        if Option.bind reread (rr_readback profile target (sq_key (sq_commitment job))) = Some (sq_commitment job)
        then RR_Exact else RR_Error)"

definition rr_compare_matches where
  "rr_compare_matches expected current \<longleftrightarrow> fst expected = fst current \<and> snd expected = snd current"

lemma rr_canonical_read_binds_actual_bytes_and_scope:
  assumes "rr_read profile target bytes = Some state" "bytes \<noteq> []"
  shows "rr_state_json state = bytes" "rr_profile state = profile" "rr_target state = target"
    "sq_sorted_keys (map sq_key (rr_receipts state))" "list_all rr_publication_origin_matches (rr_receipts state)"
  using assms by (auto simp: rr_read_def bind_eq_Some_conv split: if_splits)

lemma rr_empty_control_starts_with_no_receipt:
  "rr_readback profile target key [] = None"
  by (simp add: rr_readback_def rr_read_def rr_find_def)

lemma rr_sorted_insertion_retains_the_exact_publication:
  assumes "List.find (\<lambda>old. sq_key old = sq_key published) receipts = None"
  shows "List.find (\<lambda>old. sq_key old = sq_key published) (rr_insert published receipts) = Some published"
  using assms by (induction receipts) (auto split: if_splits)

lemma rr_existing_key_consumes_full_publication_equality:
  assumes "rr_allowed profile target dispatch_profile job"
    "rr_read profile target (snd prior_value) = Some state"
    "rr_find (sq_key (sq_commitment job)) state = Some stored"
  shows "rr_prepare profile target dispatch_profile job prior_value =
    (if stored = sq_commitment job then RR_Already_Recorded else RR_Refused)"
  using assms by (simp add: rr_prepare_def Let_def)

lemma rr_conflicting_validated_receipt_has_no_cas_plan:
  assumes "rr_allowed profile target dispatch_profile job"
    "rr_read profile target (snd prior_value) = Some state"
    "rr_find (sq_key (sq_commitment job)) state = Some stored"
    "stored \<noteq> sq_commitment job"
  shows "rr_prepare profile target dispatch_profile job prior_value = RR_Refused"
  using rr_existing_key_consumes_full_publication_equality[OF assms(1-3)] assms(4) by simp

lemma rr_missing_key_uses_the_observed_pair_and_exact_insert:
  assumes "rr_allowed profile target dispatch_profile job"
    "rr_read profile target (snd prior_value) = Some state"
    "rr_find (sq_key (sq_commitment job)) state = None"
  shows "rr_prepare profile target dispatch_profile job prior_value =
    RR_Compare prior_value (rr_state_json (state\<lparr>rr_receipts := rr_insert (sq_commitment job) (rr_receipts state)\<rparr>))"
  using assms by (simp add: rr_prepare_def Let_def)

lemma rr_different_revision_cannot_match_the_same_cas:
  "fst expected \<noteq> fst current \<Longrightarrow> \<not> rr_compare_matches expected current"
  by (simp add: rr_compare_matches_def)

lemma rr_compare_failure_returns_exact_only_after_exact_readback:
  "rr_finish profile target job RR_Compare_Failed (Some raw) = RR_Exact
    \<longleftrightarrow> rr_readback profile target (sq_key (sq_commitment job)) raw = Some (sq_commitment job)"
  by (simp add: rr_finish_def)

lemma rr_compare_failure_and_ambiguous_return_use_the_same_readback:
  "rr_finish profile target job RR_Compare_Failed reread = rr_finish profile target job RR_Ambiguous reread"
  by (simp add: rr_finish_def)

lemma rr_nested_install_and_stale_outer_return_are_conditional:
  assumes "rr_readback profile target (sq_key (sq_commitment job)) installed = Some (sq_commitment job)"
  shows "rr_finish profile target job RR_Installed None = RR_Changed"
    "rr_finish profile target job RR_Compare_Failed (Some installed) = RR_Exact"
    "rr_finish profile target job RR_Compare_Failed (Some []) = RR_Error"
  using assms by (simp_all add: rr_finish_def rr_empty_control_starts_with_no_receipt)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms rr_canonical_read_binds_actual_bytes_and_scope
    rr_empty_control_starts_with_no_receipt rr_sorted_insertion_retains_the_exact_publication
    rr_existing_key_consumes_full_publication_equality rr_conflicting_validated_receipt_has_no_cas_plan
    rr_missing_key_uses_the_observed_pair_and_exact_insert rr_different_revision_cannot_match_the_same_cas
    rr_compare_failure_returns_exact_only_after_exact_readback
    rr_compare_failure_and_ambiguous_return_use_the_same_readback rr_nested_install_and_stale_outer_return_are_conditional})
  then () else error "Unexpected oracle in receiver journal branch proofs"
\<close>

end
