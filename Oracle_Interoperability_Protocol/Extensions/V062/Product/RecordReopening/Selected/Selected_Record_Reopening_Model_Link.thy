theory Selected_Record_Reopening_Model_Link
  imports "OIP_Record_Reopening_Prefix_G0.Record_Reopening_Prefix_G0"
begin

definition srr_step where
  "srr_step srr_passed = (if srr_passed then (1::nat) else 2)"

definition srr_record_steps where
  "srr_record_steps srr_encode srr_head srr_selected srr_record =
    (if rr_record_profile srr_record \<noteq> address_profile srr_head then [2]
     else if rr_record_sequence srr_record \<noteq> address_sequence srr_head then [1,2]
     else if srr_encode (rr_record_token srr_record) \<noteq> Some srr_selected then [1,1,2]
     else [1,1,1,srr_step (rr_parent_ok srr_head (rr_record_parent srr_record))])"

definition srr_probe where
  "srr_probe srr_digest srr_parse srr_encode srr_raw srr_head =
    (let srr_selected = rr_slice srr_raw srr_head in
      if \<not> rr_span_ok srr_raw srr_head then ([2],[])
      else if srr_digest srr_selected \<noteq> Some (address_hash srr_head) then ([1,2],[])
      else case srr_parse srr_selected of
        None \<Rightarrow> ([1,1,2],[])
      | Some srr_record \<Rightarrow>
          ([1,1,1] @ srr_record_steps srr_encode srr_head srr_selected srr_record,
           [srr_step (rr_record_checks srr_encode srr_head srr_selected srr_record)]))"

definition srr_record_view where
  "srr_record_view srr_record =
    (let srr_profile = rr_record_profile srr_record;
         srr_header = [recovery_deployment srr_profile,recovery_format srr_profile,recovery_authority_profile srr_profile,
           rr_record_sequence srr_record,rr_record_token srr_record]
     in case rr_record_parent srr_record of None \<Rightarrow> [srr_header,[],[]]
        | Some srr_parent \<Rightarrow> [srr_header,rr_address_words srr_parent,address_hash srr_parent])"

definition srr_run where
  "srr_run srr_input srr_digests srr_parsed srr_encoded =
    (case srr_input of [srr_head_fields,srr_head_hash,srr_raw] \<Rightarrow>
      Option.bind (rr_make_address srr_head_fields srr_head_hash) (\<lambda>srr_head.
        let srr_digest = map_of srr_digests; srr_parse = rr_parse_graph srr_parsed; srr_encode = map_of srr_encoded;
            srr_observed = rr_record_observed True srr_digests srr_parsed srr_encoded srr_raw srr_head;
            srr_read = rr_read_record srr_digest srr_parse srr_encode srr_raw srr_head;
            srr_result = rr_observation_result srr_observed (map_option srr_record_view srr_read)
        in map_option (\<lambda>srr_returned.
            let (srr_steps,srr_checks) = srr_probe srr_digest srr_parse srr_encode srr_raw srr_head;
                srr_end = (case rr_checked_end (address_offset srr_head) (address_length srr_head) of
                    None \<Rightarrow> [] | Some srr_offset_end \<Rightarrow> [srr_offset_end]);
                srr_tail = (if srr_returned = [] then [[0],[],[],[]] else [[1]] @ srr_returned)
            in [rr_address_words srr_head,address_hash srr_head,
                [length srr_raw,length (rr_slice srr_raw srr_head)],srr_end,srr_steps,srr_checks] @ srr_tail)
          srr_result)
    | _ \<Rightarrow> None)"

definition srr_integer_abi where
  "srr_integer_abi = rr_integer_call srr_run"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      rr_checked_end_success_iff rr_checked_span_has_the_exact_slice_length
      rr_read_success_exposes_computed_guards rr_missing_external_observation_is_not_a_guard_rejection})
  then () else error "Unexpected oracle in selected record reopening link"
\<close>

export_code srr_integer_abi in SML
  module_name OIP_Selected_Record_Reopening_Link file_prefix "oip_selected_record_reopening_link"

end
