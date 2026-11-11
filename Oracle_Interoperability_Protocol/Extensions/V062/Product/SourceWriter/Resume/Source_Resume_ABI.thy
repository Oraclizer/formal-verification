theory Source_Resume_ABI
  imports Source_Resume_Link
begin

fun sr_call_from_words :: "nat \<Rightarrow> nat list \<Rightarrow> sr_call option" where
  "sr_call_from_words sr_op [] =
    (if sr_op = 1 then Some SR_Initialize else if sr_op = 3 then Some SR_Repair else None)"
| "sr_call_from_words sr_op [sr_domain,sr_event] =
    (if sr_op = 2 then Some (SR_Read (sr_domain,sr_event)) else None)"
| "sr_call_from_words _ _ = None"

fun sr_witness_from_words :: "nat \<Rightarrow> nat list list \<Rightarrow> sr_witness option" where
  "sr_witness_from_words sr_tag [[sr_mark_revision],sr_mark_digest,[],[],[],[]] =
    (if sr_tag = 1 then Some (SR_Initializing (sr_mark_revision,sr_mark_digest))
     else if sr_tag = 2 then Some (SR_Appending (sr_mark_revision,sr_mark_digest)) else None)"
| "sr_witness_from_words sr_tag [[sr_mark_revision],sr_mark_digest,[sr_observed_revision],sr_observed_digest,
       [sr_preparation_revision],sr_preparation_digest] =
    (if sr_tag = 3 then Some (SR_Repairing (sr_preparation_revision,sr_preparation_digest)
      (sr_mark_revision,sr_mark_digest) (sr_observed_revision,sr_observed_digest)) else None)"
| "sr_witness_from_words _ _ = None"

fun sr_prepare_word :: "sr_prepare \<Rightarrow> nat" where
  "sr_prepare_word (SR_Already_Prepared sr_old) = 3"
| "sr_prepare_word (SR_Replace_Journal sr_old sr_candidate) = 4"
| "sr_prepare_word SR_Prepare_Refused = 5"

fun sr_result_words ::
  "(sw_json_bytes \<Rightarrow> sw_json_bytes option) \<Rightarrow> nat list \<Rightarrow> sr_result \<Rightarrow> nat list list" where
  "sr_result_words sr_hash sr_marks SR_Invalid_Input = [[0],sr_marks]"
| "sr_result_words sr_hash sr_marks SR_Initialize_Refused = [[1],sr_marks]"
| "sr_result_words sr_hash sr_marks (SR_Read_Result sr_result) =
    (case sr_result of None \<Rightarrow> [[2,0],sr_marks] | Some sr_decision \<Rightarrow> [[2,1],sr_marks,sr_decision])"
| "sr_result_words sr_hash sr_marks (SR_Resume_Result sr_expected sr_candidate sr_condition) =
    (case sr_hash sr_candidate of None \<Rightarrow> [[0],sr_marks]
     | Some sr_digest \<Rightarrow>
         [[sr_prepare_word sr_condition],sr_marks,[fst sr_expected],snd sr_expected,sr_candidate,sr_digest])"

fun sr_case ::
  "(sw_json_bytes \<Rightarrow> sw_json_bytes option) \<Rightarrow> sw_writer_config \<Rightarrow> sw_json_bytes list \<Rightarrow>
   sw_writer_request \<Rightarrow> sw_json_bytes list list \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "sr_case sr_hash sr_cfg sr_keys sr_req sr_issuer
     [[sr_op,sr_jrev,sr_wrev,sr_tag],sr_jraw,sr_wraw,sr_primary_rev,sr_primary_sha,
      sr_observed_rev,sr_observed_sha,sr_preparation_rev,sr_preparation_sha,sr_origin_words] =
    (case (sr_call_from_words sr_op sr_origin_words,
           sr_witness_from_words sr_tag [sr_primary_rev,sr_primary_sha,sr_observed_rev,sr_observed_sha,
             sr_preparation_rev,sr_preparation_sha]) of
       (Some sr_call,Some sr_stage) \<Rightarrow>
         sr_result_words sr_hash [sr_jrev,sr_wrev]
           (sr_probe sr_hash sr_cfg sr_keys sr_req sr_issuer (sr_jrev,sr_jraw) (sr_wrev,sr_wraw) sr_call sr_stage)
     | _ \<Rightarrow> [[0]])"
| "sr_case sr_hash sr_cfg sr_keys sr_req sr_issuer _ = [[0]]"

definition sr_nat_abi ::
  "nat list list \<Rightarrow> (nat \<times> nat list) list \<Rightarrow> nat list list \<Rightarrow>
   (nat list \<times> nat list) list \<Rightarrow> nat list list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list" where
  "sr_nat_abi sr_common sr_signers sr_keys sr_hashes sr_issuer sr_observations =
    (case sr_common of
       [[sr_cd,sr_cf,sr_ca],sr_jbinding,sr_wbinding,[sr_rule_domain,sr_quorum,sr_jcap,sr_wcap],sr_epochs,sr_key,
        [sr_rd,sr_rf,sr_ra],[sr_epoch,sr_domain,sr_event,sr_asset,sr_owner,sr_dest,sr_recipient,sr_amount,sr_kind,sr_reference],
        sr_signature] \<Rightarrow>
       let sr_cfg = \<lparr>sw_cfg_profile = (sr_cd,sr_cf,sr_ca),
         sw_journal_binding_input = sr_jbinding,sw_witness_binding_input = sr_wbinding,sw_roster_domain = sr_rule_domain,
         sw_roster_epochs = sr_epochs,sw_roster_issuer = sr_key,sw_roster_quorum = sr_quorum,sw_roster_signers = sr_signers,
         sw_journal_cap = sr_jcap,sw_witness_cap = sr_wcap\<rparr>;
           sr_req = \<lparr>sw_req_profile = (sr_rd,sr_rf,sr_ra),sw_req_epoch = sr_epoch,sw_req_domain = sr_domain,
         sw_req_event = sr_event,sw_req_asset = sr_asset,sw_req_owner = sr_owner,sw_req_destination = sr_dest,
         sw_req_recipient = sr_recipient,sw_req_amount = sr_amount,sw_req_kind = sr_kind,sw_req_reference = sr_reference,
         sw_req_signature = sr_signature\<rparr>
       in map (sr_case (map_of sr_hashes) sr_cfg sr_keys sr_req sr_issuer) sr_observations
     | _ \<Rightarrow> [[[0]]])"

definition sr_integer_word :: "integer \<Rightarrow> bool" where
  "sr_integer_word sr_n \<longleftrightarrow> 0 \<le> sr_n \<and> sr_n < 18446744073709551616"

definition sr_integer_rows where
  "sr_integer_rows sr_rows \<longleftrightarrow> list_all (list_all sr_integer_word) sr_rows"

definition sr_integer_abi ::
  "integer list list \<Rightarrow> (integer \<times> integer list) list \<Rightarrow> integer list list \<Rightarrow>
   (integer list \<times> integer list) list \<Rightarrow> integer list list list \<Rightarrow>
   integer list list list \<Rightarrow> integer list list list" where
  "sr_integer_abi sr_common sr_signers sr_keys sr_hashes sr_issuer sr_observations =
    (if sr_integer_rows sr_common \<and> sr_integer_rows sr_keys \<and>
        list_all (\<lambda>(sr_id,sr_bytes). sr_integer_word sr_id \<and> list_all sr_integer_word sr_bytes) sr_signers \<and>
        list_all (\<lambda>(sr_raw,sr_sha). sr_integer_rows [sr_raw,sr_sha]) sr_hashes \<and>
        list_all sr_integer_rows sr_issuer \<and> list_all sr_integer_rows sr_observations
     then map (map (map integer_of_nat))
       (sr_nat_abi (map (map nat_of_integer) sr_common)
          (map (\<lambda>(sr_id,sr_bytes). (nat_of_integer sr_id,map nat_of_integer sr_bytes)) sr_signers)
          (map (map nat_of_integer) sr_keys)
          (map (\<lambda>(sr_raw,sr_sha). (map nat_of_integer sr_raw,map nat_of_integer sr_sha)) sr_hashes)
          (map (map (map nat_of_integer)) sr_issuer) (map (map (map nat_of_integer)) sr_observations))
     else [[[0]]])"

definition sr_publish_integer_abi ::
  "integer \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "sr_publish_integer_abi sr_revision sr_candidate sr_sha =
    (if sr_integer_word sr_revision \<and> sr_integer_rows [sr_candidate,sr_sha]
     then map_option (map integer_of_nat)
       (sr_publish_candidate (nat_of_integer sr_revision) (map nat_of_integer sr_candidate) (map nat_of_integer sr_sha))
     else None)"

export_code sr_integer_abi sr_publish_integer_abi in SML
  module_name OIP_Source_Resume_ABI file_prefix "oip_source_resume_abi"

end
