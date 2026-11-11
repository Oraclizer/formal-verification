theory Independent_Publication_Export
  imports "OIP_Independent_Publication_Check.Independent_Publication_Check"
    "OIP_Direct_Publication_Export.Direct_Publication_Export"
begin

definition ip_optional_address where
  "ip_optional_address ip_words = (if ip_words = [] then Some None
     else map_option Some (dp_address_from_words ip_words))"

definition ip_archived_lineage where
  "ip_archived_lineage ip_expected ip_previous ip_current_floor =
    (if ip_current_floor = ip_expected \<or> ip_current_floor = ip_previous then None else Some DP_Hold)"

definition ip_observe where
  "ip_observe ip_flags ip_writer_before ip_writer_after ip_expected_words ip_previous_words ip_selected_words
       ip_floor_words ip_protected_words ip_record_bytes =
    (case ip_flags of [ip_read_ok,ip_old_generation,ip_new_generation,ip_verified] \<Rightarrow>
      (if ip_read_ok > 1 \<or> ip_verified > 1 \<or> length ip_writer_before \<noteq> 32 \<or> length ip_writer_after \<noteq> 32 \<or>
          \<not> list_all (\<lambda>ip_byte. ip_byte < 256) (ip_writer_before @ ip_writer_after @ ip_record_bytes)
       then None else
       Option.bind (dp_address_from_words ip_expected_words) (\<lambda>ip_expected.
       Option.bind (dp_address_from_words ip_previous_words) (\<lambda>ip_previous.
       Option.bind (ip_optional_address ip_selected_words) (\<lambda>ip_selected.
       Option.bind (ip_optional_address ip_floor_words) (\<lambda>ip_current_floor.
       Option.bind (ip_optional_address ip_protected_words) (\<lambda>ip_current_protected.
         let ip_old = \<lparr>ip_floor = Some ip_previous, ip_protected = Some ip_previous,
                         ip_generation = ip_old_generation, ip_writer = ip_writer_before\<rparr>;
             ip_new = \<lparr>ip_floor = ip_current_floor, ip_protected = ip_current_protected,
                         ip_generation = ip_new_generation, ip_writer = ip_writer_after\<rparr>;
             ip_readback = (if ip_read_ok = 1 then Some (ip_selected,ip_new) else None)
         in Some (map (\<lambda>ip_check_generation.
           dp_reply_number (ip_select ip_check_generation ip_old ip_readback ip_expected ip_record_bytes
              (DP_Exact_Image ip_record_bytes) (ip_archived_lineage ip_expected ip_previous) (ip_verified = 1))) [True, False])))))))
     | _ \<Rightarrow> None)"

definition ip_observe_integer :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "ip_observe_integer ip_flags ip_writer_before ip_writer_after ip_expected ip_previous ip_selected ip_floor_words
     ip_protected_words ip_record =
    (if list_all (\<lambda>ip_word. 0 \<le> ip_word) (ip_flags @ ip_writer_before @ ip_writer_after @ ip_expected @
       ip_previous @ ip_selected @ ip_floor_words @ ip_protected_words @ ip_record)
     then map_option (map integer_of_nat) (ip_observe (map nat_of_integer ip_flags) (map nat_of_integer ip_writer_before)
       (map nat_of_integer ip_writer_after) (map nat_of_integer ip_expected) (map nat_of_integer ip_previous)
       (map nat_of_integer ip_selected) (map nat_of_integer ip_floor_words) (map nat_of_integer ip_protected_words)
       (map nat_of_integer ip_record)) else None)"

export_code ip_observe_integer in SML module_name OIP_Independent_Publication file_prefix "oip_independent_publication"

end
