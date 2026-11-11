theory Signed_Historical_Source_Pool_Link
  imports "OIP_Historical_Read_Export.Historical_Read_Export"
begin

definition hsp_bit :: "bool \<Rightarrow> nat" where
  "hsp_bit hsp_value = (if hsp_value then 1 else 0)"

definition hsp_pool_prefix where
  "hsp_pool_prefix hsp_domain hsp_asset hsp_input =
    (case hsp_input of [hsp_balances,hsp_funding,[hsp_registered],[hsp_locked],hsp_origins,hsp_legal] \<Rightarrow>
      if list_all (\<lambda>hsp_row. length hsp_row = 4) hsp_balances \<and>
         list_all (\<lambda>hsp_row. length hsp_row = 6) hsp_funding \<and>
         list_all (\<lambda>hsp_row. length hsp_row = 8 \<and> hsp_row ! 7 \<le> 1) (hsp_origins @ hsp_legal)
      then
        let hsp_total = sum_list (map (\<lambda>hsp_row. hsp_row ! 3)
              (filter (\<lambda>hsp_row. hsp_row ! 0 = hsp_domain \<and> hsp_row ! 1 = hsp_asset) hsp_balances));
            hsp_allocated = sum_list (map (\<lambda>hsp_row. hsp_row ! 5)
              (filter (\<lambda>hsp_row. hsp_row ! 2 = hsp_domain \<and> hsp_row ! 3 = hsp_asset) hsp_funding));
            hsp_units = hsp_total - hsp_allocated;
            hsp_present = hsp_asset \<in> set hsp_registered;
            hsp_raw_lock = hsp_asset \<in> set hsp_locked;
            hsp_touch = list_ex (\<lambda>hsp_row. hsp_row ! 0 = hsp_domain \<and> hsp_row ! 2 = hsp_asset \<and> hsp_row ! 7 = 0)
                (hsp_origins @ hsp_legal)
        in if hsp_total < 2^128 \<and> hsp_allocated < 2^128 \<and> hsp_allocated \<le> hsp_total \<and> hsp_units < 2^64
           then Some (\<lparr>historical_units = hsp_units,historical_locked = False,
                 historical_unpublished_touch = hsp_touch,historical_registered = hsp_present\<rparr>,
               [hsp_total,hsp_allocated,hsp_units,hsp_bit hsp_present,hsp_bit hsp_raw_lock,hsp_bit hsp_touch])
           else None
      else None
    | _ \<Rightarrow> None)"

fun hsp_prefixes where
  "hsp_prefixes hsp_domain hsp_asset [] = Some []"
| "hsp_prefixes hsp_domain hsp_asset (hsp_head # hsp_tail) =
    Option.bind (hsp_pool_prefix hsp_domain hsp_asset hsp_head) (\<lambda>hsp_projection.
      map_option (\<lambda>hsp_rest. hsp_projection # hsp_rest) (hsp_prefixes hsp_domain hsp_asset hsp_tail))"

definition hsp_trace where
  "hsp_trace hsp_raw hsp_metadata hsp_history =
    (case (hsp_raw,hsp_metadata) of
      ([hsp_bytes,hsp_exact_core,hsp_preimage,hsp_signature],
       [hsp_principal,hsp_key,hsp_source,hsp_deployment,hsp_session,hsp_epoch,hsp_target,
        hsp_domain,hsp_asset,hsp_revision,hsp_live_epoch,hsp_live_revision]) \<Rightarrow>
      if \<not> list_all (\<lambda>hsp_byte. hsp_byte < 256) (hsp_bytes @ hsp_exact_core @ hsp_preimage @ hsp_signature)
      then None
      else Option.bind (decode_wire_packet hsp_bytes) (\<lambda>hsp_packet.
        let hsp_core = packet_core hsp_packet in
        if encode_wire_packet hsp_packet \<noteq> hsp_bytes \<or> encode_wire_core hsp_core \<noteq> hsp_exact_core \<or>
           envelope_signing_bytes hsp_core \<noteq> hsp_preimage \<or> packet_signature hsp_packet \<noteq> hsp_signature
        then None
        else (case code_source_nonreceipt_read_service (0::nat) hsp_core of
          Some (Service_Read _ hsp_proof hsp_decoded_target (Historical_Data
              (Source_Balance (hsp_decoded_domain,hsp_decoded_asset)) hsp_decoded_revision) None) \<Rightarrow>
            (let hsp_selector = [wire_principal hsp_core,wire_key_number hsp_core,wire_source_domain hsp_core,
                  wire_deployment hsp_core,proof_session hsp_proof,proof_epoch hsp_proof,hsp_decoded_target,
                  hsp_decoded_domain,hsp_decoded_asset,hsp_decoded_revision]
             in if hsp_selector \<noteq> take 10 hsp_metadata \<or> hsp_live_epoch \<noteq> hsp_epoch \<or>
                   length hsp_history \<noteq> Suc hsp_live_revision then None
                else map_option (\<lambda>hsp_rows.
                  let hsp_prefix_values = map fst hsp_rows;
                      hsp_normal = historical_native_read False True True hsp_decoded_revision hsp_prefix_values;
                      hsp_unavailable = historical_native_read False True False hsp_decoded_revision hsp_prefix_values;
                      hsp_diagnostic = historical_native_read True True True hsp_decoded_revision hsp_prefix_values
                  in [hsp_selector,encode_wire_core hsp_core,[hsp_live_epoch,hsp_live_revision],
                       historical_export_reply hsp_normal,historical_export_reply hsp_unavailable,
                       historical_export_reply hsp_diagnostic] @
                     map (\<lambda>(hsp_index,hsp_row). hsp_index # snd hsp_row) (zip [0..<length hsp_rows] hsp_rows))
                  (hsp_prefixes hsp_decoded_domain hsp_decoded_asset hsp_history))
        | _ \<Rightarrow> None))
    | _ \<Rightarrow> None)"

definition hsp_u64 :: "integer \<Rightarrow> bool" where
  "hsp_u64 hsp_word \<longleftrightarrow> 0 \<le> hsp_word \<and> hsp_word < 18446744073709551616"

definition hsp_integer_abi ::
  "integer list list \<Rightarrow> integer list \<Rightarrow> integer list list list list \<Rightarrow> integer list list option" where
  "hsp_integer_abi hsp_raw hsp_metadata hsp_history =
    (if list_all (list_all hsp_u64) hsp_raw \<and> list_all hsp_u64 hsp_metadata \<and>
        list_all (list_all (list_all (list_all hsp_u64))) hsp_history
     then map_option (map (map integer_of_nat))
       (hsp_trace (map (map nat_of_integer) hsp_raw) (map nat_of_integer hsp_metadata)
         (map (map (map (map nat_of_integer))) hsp_history))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms historical_read_reuses_exact_named_reference_prefix
      the_native_cut_and_its_selected_prefixes_give_the_same_model_values
      historical_export_does_not_label_a_historical_value_current})
  then () else error "Unexpected oracle in the Historical SourcePool link"
\<close>

export_code hsp_integer_abi in SML
  module_name OIP_Signed_Historical_Source_Pool_Link file_prefix "oip_signed_historical_source_pool_link"

end
