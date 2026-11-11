theory Direct_Publication_Export
  imports "OIP_Direct_Publication_Check.Direct_Publication_Check"
begin

fun dp_address_from_words :: "nat list \<Rightarrow> nat list dp_address option" where
  "dp_address_from_words (dp_deployment # dp_format # dp_authority # dp_sequence # dp_offset # dp_length # dp_digest) =
    (if length dp_digest = 32 \<and> list_all (\<lambda>dp_byte. dp_byte < 256) dp_digest then
      Some (\<lparr>head_profile = \<lparr>recovery_deployment = dp_deployment, recovery_format = dp_format,
              recovery_authority_profile = dp_authority\<rparr>, head_sequence = dp_sequence, head_digest = dp_digest\<rparr>,
              dp_offset, dp_length) else None)"
| "dp_address_from_words _ = None"

fun dp_reply_number where
  "dp_reply_number DP_Selected = (0::nat)"
| "dp_reply_number (DP_Stopped DP_Hold) = 1"
| "dp_reply_number (DP_Stopped DP_Invalid_Image) = 2"
| "dp_reply_number (DP_Stopped DP_IO) = 3"
| "dp_reply_number (DP_Stopped (DP_Publication dp_code)) = 4 + dp_code"

definition dp_status_from_number where
  "dp_status_from_number (dp_status::nat) = map_of
    [(0, DP_Cas_OK), (1, DP_Cas_Uncertain), (2, DP_Known_Refusal DP_Hold)] dp_status"

definition dp_observe where
  "dp_observe dp_status dp_candidate dp_head_words dp_expected_record dp_image_bytes =
    Option.bind (dp_status_from_number dp_status) (\<lambda>dp_cas_status.
    Option.bind (dp_address_from_words dp_candidate) (\<lambda>dp_expected.
    Option.bind (if dp_head_words = [] then Some None else map_option Some (dp_address_from_words dp_head_words)) (\<lambda>dp_current.
      Some (map (\<lambda>dp_check.
        dp_reply_number (dp_after_cas dp_check dp_cas_status dp_expected dp_current dp_expected_record
          (DP_Exact_Image dp_image_bytes))) [True, False]))))"

definition dp_observe_integer :: "integer \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "dp_observe_integer dp_status dp_candidate dp_current dp_expected_record dp_image_bytes =
    (if 0 \<le> dp_status \<and> list_all (\<lambda>dp_word. 0 \<le> dp_word) (dp_candidate @ dp_current) \<and>
        list_all (\<lambda>dp_byte. 0 \<le> dp_byte \<and> dp_byte < 256) (dp_expected_record @ dp_image_bytes)
     then map_option (map integer_of_nat) (dp_observe (nat_of_integer dp_status)
       (map nat_of_integer dp_candidate) (map nat_of_integer dp_current)
       (map nat_of_integer dp_expected_record) (map nat_of_integer dp_image_bytes)) else None)"

lemma dp_exact_offset_is_part_of_selected_address:
  "dp_confirm True (dp_head,dp_offset,dp_length) (Some (dp_head,dp_other_offset,dp_length))
    dp_record (DP_Exact_Image dp_record) = (if dp_offset = dp_other_offset then DP_Selected else DP_Stopped DP_Hold)"
  by (simp add: dp_confirm_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms dp_exact_offset_is_part_of_selected_address}) then ()
  else error "Unexpected oracle in direct publication export"
\<close>

export_code dp_observe_integer in SML module_name OIP_Direct_Publication file_prefix "oip_direct_publication"

end
