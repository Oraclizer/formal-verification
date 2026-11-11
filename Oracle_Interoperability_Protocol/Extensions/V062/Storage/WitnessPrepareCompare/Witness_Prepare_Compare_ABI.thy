theory Witness_Prepare_Compare_ABI
  imports Witness_Prepare_Compare_Link
begin

fun wpc_parse_view :: "nat list list list \<Rightarrow> wpc_prepare_view option" where
  "wpc_parse_view [[wpc_profile,[wpc_revision],wpc_digest,wpc_raw,wpc_canonical],wpc_rows] =
    (if length wpc_profile = 3 \<and> length wpc_digest = 32 \<and>
       list_all (\<lambda>wpc_byte. wpc_byte < 256) (wpc_raw @ wpc_canonical @ wpc_digest @ concat wpc_rows)
     then Some \<lparr>wpc_raw_prepare = wpc_raw,wpc_reencoded_prepare = wpc_canonical,
       wpc_prepare_profile = wpc_profile,wpc_prepare_base = (wpc_revision,wpc_digest),wpc_preparations = wpc_rows\<rparr>
     else None)"
| "wpc_parse_view _ = None"

fun wpc_parse_hashes :: "nat list list list \<Rightarrow> (nat list \<times> nat list) list option" where
  "wpc_parse_hashes [] = Some []"
| "wpc_parse_hashes ([wpc_raw,wpc_digest] # wpc_rest) =
    (if length wpc_digest = 32 \<and> list_all (\<lambda>wpc_byte. wpc_byte < 256) wpc_digest
     then map_option (Cons (wpc_raw,wpc_digest)) (wpc_parse_hashes wpc_rest) else None)"
| "wpc_parse_hashes _ = None"

definition wpc_prediction_rows where
  "wpc_prediction_rows wpc_pred wpc_counts wpc_revisions wpc_digest =
    (case wpc_pred of WPC_Invalid_Plan \<Rightarrow> [[0]]
     | WPC_No_Target_On_Compare_False \<Rightarrow> [1 # wpc_counts,wpc_revisions,wpc_digest]
     | WPC_Exact_Target_On_Compare_False wpc_target \<Rightarrow> [2 # wpc_counts,wpc_revisions,wpc_digest,wpc_target])"

definition wpc_nat_abi ::
  "nat list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list \<Rightarrow>
   nat list list list \<Rightarrow> nat list list list \<Rightarrow> nat list list" where
  "wpc_nat_abi wpc_header wpc_before_rows wpc_original_rows wpc_contender_rows wpc_hash_rows =
    (case wpc_header of [[wpc_arev,wpc_wrev,wpc_prev_rev,wpc_cap,wpc_limit],wpc_selected_raw,wpc_profile,
        wpc_digest,wpc_prev_digest,wpc_target,wpc_contender] \<Rightarrow>
       (case (wpc_parse_view wpc_before_rows,wpc_parse_view wpc_original_rows,
              wpc_parse_view wpc_contender_rows,wpc_parse_hashes wpc_hash_rows) of
         (Some wpc_initial,Some wpc_original_intent,Some wpc_contender_intent,Some wpc_hashes) \<Rightarrow>
           let wpc_current = \<lparr>wpc_current_raw = wpc_selected_raw,wpc_current_profile = wpc_profile,
             wpc_current_mark = (wpc_wrev,wpc_digest),wpc_current_parent = Some (wpc_prev_rev,wpc_prev_digest)\<rparr>
           in if 0 < wpc_arev \<and> wpc_arev < 2^63 \<and> 0 < wpc_wrev \<and> 0 < wpc_prev_rev \<and>
                 length wpc_profile = 3 \<and> length wpc_prev_digest = 32 \<and>
                 list_all (\<lambda>wpc_byte. wpc_byte < 256) (wpc_target @ wpc_contender @ wpc_selected_raw @ wpc_prev_digest) \<and>
                 map_of wpc_hashes wpc_selected_raw = Some wpc_digest
              then wpc_prediction_rows
                 (wpc_predict wpc_limit wpc_cap wpc_current wpc_initial wpc_target wpc_contender
                    wpc_original_intent wpc_contender_intent)
                 [length (wpc_preparations wpc_initial),length (wpc_preparations wpc_original_intent),
                   length (wpc_preparations wpc_contender_intent)] [wpc_arev,wpc_wrev] wpc_digest
              else [[0]]
       | _ \<Rightarrow> [[0]])
      | _ \<Rightarrow> [[0]])"

definition wpc_integer_word :: "integer \<Rightarrow> bool" where
  "wpc_integer_word wpc_n \<longleftrightarrow> 0 \<le> wpc_n \<and> wpc_n < 18446744073709551616"

definition wpc_integer_rows where
  "wpc_integer_rows wpc_rows \<longleftrightarrow> list_all (list_all wpc_integer_word) wpc_rows"

definition wpc_integer_abi ::
  "integer list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list \<Rightarrow>
   integer list list list \<Rightarrow> integer list list list \<Rightarrow> integer list list" where
  "wpc_integer_abi wpc_header wpc_before_rows wpc_original_rows wpc_contender_rows wpc_hash_rows =
    (if wpc_integer_rows wpc_header \<and>
        list_all (list_all wpc_integer_rows) [wpc_before_rows,wpc_original_rows,wpc_contender_rows,wpc_hash_rows]
     then map (map integer_of_nat)
       (wpc_nat_abi (map (map nat_of_integer) wpc_header)
          (map (map (map nat_of_integer)) wpc_before_rows) (map (map (map nat_of_integer)) wpc_original_rows)
          (map (map (map nat_of_integer)) wpc_contender_rows) (map (map (map nat_of_integer)) wpc_hash_rows))
     else [[0]])"

export_code wpc_integer_abi in SML
  module_name OIP_Witness_Prepare_Compare_ABI file_prefix "oip_witness_prepare_compare_abi"

end
