theory Source_Commitment_Resume_ABI
  imports Source_Commitment_Resume_Link
begin

fun sc_collect :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "sc_collect sc_f [] = Some []"
| "sc_collect sc_f (sc_x # sc_xs) =
     Option.bind (sc_f sc_x) (\<lambda>sc_y. map_option (Cons sc_y) (sc_collect sc_f sc_xs))"

fun sc_signer_row :: "nat list \<Rightarrow> (nat \<times> sw_json_bytes) option" where
  "sc_signer_row (sc_id # sc_raw) = (if sw_octets_of_length 32 sc_raw then Some (sc_id,sc_raw) else None)"
| "sc_signer_row _ = None"

fun sc_roster_row :: "nat list list \<Rightarrow> sc_roster_entry option" where
  "sc_roster_row ([sc_domain,sc_epoch,sc_roster,sc_quorum] # sc_issuer # sc_signers) =
    map_option (\<lambda>sc_keys. \<lparr>sc_rule_domain = sc_domain,sc_rule_epoch = sc_epoch,sc_rule_id = sc_roster,
      sc_rule_issuer = sc_issuer,sc_rule_quorum = sc_quorum,sc_rule_signers = sc_keys\<rparr>) (sc_collect sc_signer_row sc_signers)"
| "sc_roster_row _ = None"

fun sc_record_row :: "nat list list \<Rightarrow> supplier_signed_record option" where
  "sc_record_row [sc_statement,sc_sig] =
    (if sw_octets_of_length 64 sc_sig \<and> list_all (\<lambda>sc_b. sc_b < 256) sc_statement
     then Some \<lparr>supplier_record_statement = sc_statement,supplier_record_signature = sc_sig\<rparr> else None)"
| "sc_record_row _ = None"

fun sc_hash_row :: "nat list list \<Rightarrow> (sw_json_bytes \<times> sw_json_bytes) option" where
  "sc_hash_row [sc_raw,sc_sha] = (if sw_octets_of_length 32 sc_sha then Some (sc_raw,sc_sha) else None)"
| "sc_hash_row _ = None"

fun sc_witness_row ::
  "nat \<Rightarrow> sc_source_state \<Rightarrow> sw_json_mark \<Rightarrow> nat list list list \<Rightarrow> sc_witness option" where
  "sc_witness_row sc_tag sc_state sc_m [] = (if sc_tag = 2 then Some (SC_Selected sc_state sc_m) else None)"
| "sc_witness_row sc_tag sc_state sc_m [sc_record] =
     (if sc_tag = 1 then map_option (SC_Appending sc_state sc_m) (sc_record_row sc_record) else None)"
| "sc_witness_row _ _ _ _ = None"

fun sc_prepare_word :: "sr_prepare \<Rightarrow> nat" where
  "sc_prepare_word (SR_Already_Prepared sc_old) = 1"
| "sc_prepare_word (SR_Replace_Journal sc_old sc_candidate) = 2"
| "sc_prepare_word SR_Prepare_Refused = 3"

fun sc_result_words :: "nat list \<Rightarrow> sc_result \<Rightarrow> nat list list" where
  "sc_result_words sc_revs SC_Outside_Scope = [[0],sc_revs]"
| "sc_result_words sc_revs SC_Invalid_Input = [[1],sc_revs]"
| "sc_result_words sc_revs (SC_Reservation_Mismatch sc_can_extend) =
     [[2,if sc_can_extend then 1 else 0],sc_revs]"
| "sc_result_words sc_revs (SC_Resume sc_wmark sc_candidate sc_condition) =
     [[3,sc_prepare_word sc_condition],sc_revs,[fst sc_wmark],snd sc_wmark,sc_candidate]"
| "sc_result_words sc_revs SC_Exact_Selected_Retry = [[4],sc_revs]"
| "sc_result_words sc_revs SC_Selected_Mismatch = [[5],sc_revs]"

fun sc_case ::
  "(sw_json_bytes \<times> sw_json_bytes) list \<Rightarrow> sw_json_bytes sync_verify \<Rightarrow> sw_json_profile \<Rightarrow>
    sw_json_bytes \<Rightarrow> sw_json_bytes supplier_registrations \<Rightarrow> nat list list list list \<Rightarrow> nat list list" where
  "sc_case sc_common_hashes sc_verify sc_profile sc_stores sc_rules
     [[[[sc_tag,sc_jrev,sc_wrev,sc_prep_rev,sc_selected_rev],sc_jraw,sc_wraw,sc_prep_sha,sc_selected_sha]],
       [sc_request_words],sc_reserved_words,sc_records,sc_before_hashes] =
    (case (sc_record_row sc_request_words,sc_collect sc_record_row sc_records,sc_collect sc_hash_row sc_before_hashes) of
       (Some sc_request,Some sc_prior,Some sc_local_hashes) \<Rightarrow>
         let sc_before = \<lparr>sc_preparation = (sc_prep_rev,sc_prep_sha),sc_commitments = sc_prior\<rparr>;
             sc_hash = map_of (sc_common_hashes @ sc_local_hashes)
         in if sc_jrev = 0 \<or> sc_wrev = 0 then [[1],[sc_jrev,sc_wrev]]
            else (case sc_witness_row sc_tag sc_before (sc_selected_rev,sc_selected_sha) sc_reserved_words of
               None \<Rightarrow> [[1],[sc_jrev,sc_wrev]]
             | Some sc_witness \<Rightarrow> sc_result_words [sc_jrev,sc_wrev]
                 (sc_probe sc_hash sc_verify sc_profile sc_stores sc_rules (sc_jrev,sc_jraw)
                   (sc_wrev,sc_wraw) sc_witness sc_request))
     | _ \<Rightarrow> [[1]])"
| "sc_case sc_common_hashes sc_verify sc_profile sc_stores sc_rules _ = [[1]]"

definition sc_nat_abi ::
  "nat list list \<Rightarrow> nat list list list \<Rightarrow> nat list list \<Rightarrow> nat list list list \<Rightarrow>
    nat list list list \<Rightarrow> nat list list list list list \<Rightarrow> nat list list list" where
  "sc_nat_abi sc_config sc_registry_rows sc_good_keys sc_crypto_facts sc_common_hash_rows sc_observations =
    (case sc_config of [[sc_deploy,sc_format,sc_authority,sc_domain],sc_jpreimage,sc_wpreimage,sc_registry_raw] \<Rightarrow>
       (case (sc_collect sc_roster_row sc_registry_rows,sc_collect sc_hash_row sc_common_hash_rows) of
          (Some sc_rows,Some sc_common_hashes) \<Rightarrow>
            if sw_profile_width (sc_deploy,sc_format,sc_authority) \<and> sc_registry_valid sc_good_keys sc_registry_raw sc_domain sc_rows
            then (case sc_registered_stores (map_of sc_common_hashes) sc_jpreimage sc_wpreimage sc_registry_raw of
                None \<Rightarrow> [[[1]]]
              | Some sc_stores \<Rightarrow> map (sc_case sc_common_hashes
                  (\<lambda>sc_k sc_p sc_s. List.member sc_crypto_facts [sc_k,sc_p,sc_s])
                  (sc_deploy,sc_format,sc_authority) sc_stores (sc_configured_rules sc_rows)) sc_observations)
            else [[[1]]]
        | _ \<Rightarrow> [[[1]]])
     | _ \<Rightarrow> [[[1]]])"

definition sc_integer_word :: "integer \<Rightarrow> bool" where
  "sc_integer_word sc_n \<longleftrightarrow> 0 \<le> sc_n \<and> sc_n < 18446744073709551616"

definition sc_integer_rows where
  "sc_integer_rows sc_input \<longleftrightarrow> list_all (list_all sc_integer_word) sc_input"

definition sc_integer_abi ::
  "integer list list \<Rightarrow> integer list list list \<Rightarrow> integer list list \<Rightarrow> integer list list list \<Rightarrow>
    integer list list list \<Rightarrow> integer list list list list list \<Rightarrow> integer list list list" where
  "sc_integer_abi sc_config sc_registry_rows sc_good_keys sc_crypto_facts sc_common_hash_rows sc_observations =
    (if sc_integer_rows sc_config \<and> sc_integer_rows sc_good_keys \<and>
        list_all (list_all sc_integer_rows) [sc_registry_rows,sc_crypto_facts,sc_common_hash_rows] \<and>
        list_all (list_all (list_all sc_integer_rows)) sc_observations
     then map (map (map integer_of_nat))
       (sc_nat_abi (map (map nat_of_integer) sc_config) (map (map (map nat_of_integer)) sc_registry_rows)
         (map (map nat_of_integer) sc_good_keys) (map (map (map nat_of_integer)) sc_crypto_facts)
         (map (map (map nat_of_integer)) sc_common_hash_rows) (map (map (map (map (map nat_of_integer)))) sc_observations))
     else [[[1]]])"

export_code sc_integer_abi in SML
  module_name OIP_Source_Commitment_Resume_ABI file_prefix "oip_source_commitment_resume_abi"

end
