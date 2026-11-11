theory Source_Commitment_Resume_Link
  imports "OIP_Source_Resume_Link.Source_Resume_Link"
    "OIP_Sync_V061_Concrete_Supplier_V2.Sync_V061_Supplier_Readback"
begin

text \<open>Commitment-only selected Source states with one registered origin
  and one roster per epoch. The existing supplier model authenticates each
  exact signed statement and replays its stream and origin event. This leaf
  adds the Source state and witness encodings and the reservation choice.
  Replacement and selected readback are physical conditions.\<close>

record sc_roster_entry =
  sc_rule_domain :: nat
  sc_rule_epoch :: nat
  sc_rule_id :: nat
  sc_rule_issuer :: sw_json_bytes
  sc_rule_quorum :: nat
  sc_rule_signers :: "(nat \<times> sw_json_bytes) list"

definition sc_roster_key where
  "sc_roster_key sc_row = (sc_rule_domain sc_row,sc_rule_epoch sc_row,sc_rule_id sc_row)"

definition sc_configured_rules where
  "sc_configured_rules sc_rows sc_key =
    map_option (\<lambda>sc_row. \<lparr>supplier_record_issuer = sc_rule_issuer sc_row,
        supplier_roster_quorum = sc_rule_quorum sc_row,supplier_roster_signers = map_of (sc_rule_signers sc_row)\<rparr>)
      (map_of (map (\<lambda>sc_row. (sc_roster_key sc_row,sc_row)) sc_rows) sc_key)"

definition sc_roster_valid where
  "sc_roster_valid sc_keys sc_row \<longleftrightarrow>
     sw_u64_words [sc_rule_domain sc_row,sc_rule_epoch sc_row,sc_rule_id sc_row] \<and>
     0 < sc_rule_quorum sc_row \<and> sc_rule_quorum sc_row \<le> length (sc_rule_signers sc_row) \<and>
     sw_u64_words (map fst (sc_rule_signers sc_row)) \<and> sorted_wrt (<) (map fst (sc_rule_signers sc_row)) \<and>
     distinct (sc_rule_issuer sc_row # map snd (sc_rule_signers sc_row)) \<and>
     list_all (\<lambda>sc_k. sw_octets_of_length 32 sc_k \<and> List.member sc_keys sc_k)
       (sc_rule_issuer sc_row # map snd (sc_rule_signers sc_row))"

definition sc_roster_json where
  "sc_roster_json sc_row =
     code_json_open_key ''issuer'' @ sw_json_octets (sc_rule_issuer sc_row) @
     code_json_next_key ''quorum'' @ sw_decimal (sc_rule_quorum sc_row) @
     code_json_next_key ''signers'' @ [123] @
     sw_json_elements (map (\<lambda>(sc_id,sc_key). sw_json_numeric_entry sc_id (sw_json_octets sc_key))
       (sc_rule_signers sc_row)) @ [125,125]"

definition sc_registry_json where
  "sc_registry_json sc_domain sc_rows =
     [123] @ sw_json_numeric_entry sc_domain
       ([123] @ sw_json_elements (map (\<lambda>sc_row. sw_json_numeric_entry (sc_rule_epoch sc_row)
         ([123] @ sw_json_numeric_entry (sc_rule_id sc_row) (sc_roster_json sc_row) @ [125])) sc_rows) @ [125]) @ [125]"

definition sc_registry_valid where
  "sc_registry_valid sc_keys sc_raw sc_domain sc_rows \<longleftrightarrow>
     sc_rows \<noteq> [] \<and> list_all (\<lambda>sc_row. sc_rule_domain sc_row = sc_domain \<and> sc_roster_valid sc_keys sc_row) sc_rows \<and>
     sorted_wrt (<) (map sc_rule_epoch sc_rows) \<and> sc_registry_json sc_domain sc_rows = sc_raw"

definition sc_stores_json where
  "sc_stores_json sc_j sc_w sc_term sc_commitment =
    (let sc_base = sw_stores_json sc_j sc_w sc_term in
      take (length sc_base - 1) sc_base @ code_json_next_key ''commitment_authorities'' @
        sw_json_octets sc_commitment @ [125])"

definition sc_registered_stores where
  "sc_registered_stores sc_hash sc_jinput sc_winput sc_registry_raw =
    (let sc_j = sw_digest sc_hash sc_jinput; sc_w = sw_digest sc_hash sc_winput;
         sc_terminal = sw_digest sc_hash [123,125]; sc_commitment = sw_digest sc_hash sc_registry_raw
     in if sc_jinput \<noteq> sc_winput \<and> list_all (sw_octets_of_length 32) [sc_j,sc_w,sc_terminal,sc_commitment]
        then Some (sc_stores_json sc_j sc_w sc_terminal sc_commitment) else None)"

definition sc_signed_json where
  "sc_signed_json sc_record =
     code_json_open_key ''statement'' @ sw_json_octets (supplier_record_statement sc_record) @
     code_json_next_key ''signature'' @ sw_json_octets (supplier_record_signature sc_record) @ [125]"

record sc_source_state =
  sc_preparation :: sw_json_mark
  sc_commitments :: "supplier_signed_record list"

definition sc_state_json where
  "sc_state_json sc_profile sc_stores sc_state =
    (let sc_base = sw_state_json sc_profile sc_stores (Some (sc_preparation sc_state)) [] in
      take (length sc_base - 1) sc_base @ code_json_next_key ''commitments'' @
      sw_json_array (map sc_signed_json (sc_commitments sc_state)) @ [125])"

definition sc_appending_json where
  "sc_appending_json sc_before sc_mark sc_reserved =
    code_json_open_key ''AppendingCommitment'' @
    code_json_open_key ''before'' @ sw_selected_body_json sc_before sc_mark @
    code_json_next_key ''commitment'' @ sc_signed_json sc_reserved @ [125,125]"

definition sc_replay_valid where
  "sc_replay_valid sc_verify sc_deploy sc_rules sc_records \<longleftrightarrow>
    (case supplier_replay_commitments sc_verify sc_deploy sc_rules sc_records
       \<lparr>supplier_tips = (\<lambda>_. None),supplier_events = {}\<rparr> of None \<Rightarrow> False | Some _ \<Rightarrow> True)"

definition sc_state_valid where
  "sc_state_valid sc_verify sc_deploy sc_rules sc_state \<longleftrightarrow>
    sc_commitments sc_state \<noteq> [] \<and> sr_mark_width (sc_preparation sc_state) \<and>
    sc_replay_valid sc_verify sc_deploy sc_rules (sc_commitments sc_state)"

definition sc_latest_signed where
  "sc_latest_signed sc_records sc_stream =
    List.find (\<lambda>sc_record.
      map_option sync_source_stream_of (supplier_decode_statement (supplier_record_statement sc_record)) = Some sc_stream)
      (rev sc_records)"

datatype sc_witness =
    SC_Appending sc_source_state sw_json_mark supplier_signed_record
  | SC_Selected sc_source_state sw_json_mark

datatype sc_result =
    SC_Outside_Scope
  | SC_Invalid_Input
  | SC_Reservation_Mismatch bool
  | SC_Resume sw_json_mark sw_json_bytes sr_prepare
  | SC_Exact_Selected_Retry
  | SC_Selected_Mismatch

definition sc_resume_reserved where
  "sc_resume_reserved sc_hash sc_profile sc_stores sc_journal sc_witness_raw sc_before sc_selected_mark
      sc_reserved sc_request sc_request_replay =
    (if sc_request \<noteq> sc_reserved then SC_Reservation_Mismatch sc_request_replay
     else case sr_mark sc_hash sc_witness_raw of None \<Rightarrow> SC_Invalid_Input
      | Some sc_witness_mark \<Rightarrow>
        let sc_prepared = \<lparr>sc_preparation = sc_witness_mark,sc_commitments = sc_commitments sc_before @ [sc_request]\<rparr>;
            sc_candidate = sc_state_json sc_profile sc_stores sc_prepared
        in SC_Resume sc_witness_mark sc_candidate (sr_prepare sc_hash sc_journal sc_selected_mark sc_candidate))"

lemma sc_a_different_signed_record_cannot_resume_the_reservation:
  assumes "sc_request \<noteq> sc_reserved"
  shows "sc_resume_reserved sc_hash sc_profile sc_stores sc_journal sc_witness_raw sc_before sc_selected_mark
      sc_reserved sc_request sc_request_replay = SC_Reservation_Mismatch sc_request_replay"
  using assms by (simp add: sc_resume_reserved_def)

lemma sc_resume_uses_the_exact_witness_mark_and_original_signed_record:
  assumes "sc_resume_reserved sc_hash sc_profile sc_stores sc_journal sc_witness_raw sc_before sc_selected_mark
      sc_reserved sc_request sc_request_replay = SC_Resume sc_mark sc_bytes sc_prepare"
  shows "sc_request = sc_reserved" "sr_mark sc_hash sc_witness_raw = Some sc_mark"
    "sc_bytes = sc_state_json sc_profile sc_stores
       \<lparr>sc_preparation = sc_mark,sc_commitments = sc_commitments sc_before @ [sc_reserved]\<rparr>"
  using assms by (auto simp: sc_resume_reserved_def Let_def split: option.splits if_splits)

definition sc_selected_retry where
  "sc_selected_retry sc_before sc_statement sc_request sc_request_replay =
    (if sc_request_replay then SC_Outside_Scope
     else if sc_latest_signed (sc_commitments sc_before) (sync_source_stream_of sc_statement) = Some sc_request
     then SC_Exact_Selected_Retry else SC_Selected_Mismatch)"

lemma sc_selected_retry_requires_failed_extension_and_the_exact_latest_record:
  assumes "sc_selected_retry sc_before sc_statement sc_request sc_request_replay = SC_Exact_Selected_Retry"
  shows "\<not> sc_request_replay"
    "sc_latest_signed (sc_commitments sc_before) (sync_source_stream_of sc_statement) = Some sc_request"
  using assms by (auto simp: sc_selected_retry_def split: if_splits)

definition sc_probe where
  "sc_probe sc_hash sc_verify sc_profile sc_stores sc_rules sc_journal sc_witness_raw sc_witness sc_request =
    (let sc_deploy = fst sc_profile in
     case supplier_authenticated_commitment sc_verify sc_deploy sc_rules sc_request of None \<Rightarrow> SC_Invalid_Input
      | Some sc_statement \<Rightarrow>
       (case sc_witness of
         SC_Appending sc_before sc_selected_mark sc_reserved \<Rightarrow>
           let sc_before_bytes = sc_state_json sc_profile sc_stores sc_before;
               sc_old_records = sc_commitments sc_before
           in if sc_state_valid sc_verify sc_deploy sc_rules sc_before \<and> sr_mark_names sc_hash sc_before_bytes sc_selected_mark \<and>
                 snd sc_witness_raw = sc_appending_json sc_before_bytes sc_selected_mark sc_reserved \<and>
                 sc_replay_valid sc_verify sc_deploy sc_rules (sc_old_records @ [sc_reserved])
              then sc_resume_reserved sc_hash sc_profile sc_stores sc_journal sc_witness_raw sc_before sc_selected_mark sc_reserved
                sc_request (sc_replay_valid sc_verify sc_deploy sc_rules (sc_old_records @ [sc_request]))
              else SC_Invalid_Input
        | SC_Selected sc_before sc_selected_mark \<Rightarrow>
           let sc_before_bytes = sc_state_json sc_profile sc_stores sc_before
           in if sc_state_valid sc_verify sc_deploy sc_rules sc_before \<and> sr_mark_names sc_hash sc_before_bytes sc_selected_mark \<and>
                 snd sc_journal = sc_before_bytes \<and> sr_mark sc_hash sc_journal = Some sc_selected_mark \<and>
                 snd sc_witness_raw = sw_selected_json sc_before_bytes sc_selected_mark
              then sc_selected_retry sc_before sc_statement sc_request
                (sc_replay_valid sc_verify sc_deploy sc_rules (sc_commitments sc_before @ [sc_request]))
              else SC_Invalid_Input))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sc_a_different_signed_record_cannot_resume_the_reservation
    sc_resume_uses_the_exact_witness_mark_and_original_signed_record
    sc_selected_retry_requires_failed_extension_and_the_exact_latest_record
    supplier_authenticated_record_consumes_exact_statement_and_registered_issuer
    supplier_append_checks_event_and_reuses_monotone_source_append})
  then () else error "Unexpected oracle in exact Source commitment resume"
\<close>

end
