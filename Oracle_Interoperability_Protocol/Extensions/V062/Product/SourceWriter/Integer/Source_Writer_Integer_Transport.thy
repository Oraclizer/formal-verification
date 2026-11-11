theory Source_Writer_Integer_Transport
  imports "OIP_Source_Writer_Phases.Source_Writer_ABI"
begin

text \<open>The checked phase entry uses the generated abstract nat type.
  This leaf exposes only checked conversion of external integer arguments
  and the exact result rows of that entry.\<close>

definition sw_external_word :: "integer \<Rightarrow> bool" where
  "sw_external_word sw_n \<longleftrightarrow> 0 \<le> sw_n \<and> sw_n < 18446744073709551616"

definition sw_external_rows :: "integer list list \<Rightarrow> bool" where
  "sw_external_rows sw_input \<longleftrightarrow> list_all (list_all sw_external_word) sw_input"

definition sw_observe_integer ::
  "integer list list \<Rightarrow> (integer \<times> integer list) list \<Rightarrow> integer list list \<Rightarrow>
   (integer list \<times> integer list) list \<Rightarrow> integer list list list \<Rightarrow> integer list list" where
  "sw_observe_integer sw_rows sw_signers sw_good_keys sw_hash_rows sw_issuer_facts =
    (if sw_external_rows sw_rows \<and> sw_external_rows sw_good_keys \<and>
        list_all (\<lambda>(sw_id,sw_key). sw_external_word sw_id \<and> list_all sw_external_word sw_key) sw_signers \<and>
        list_all (\<lambda>(sw_raw,sw_d). sw_external_rows [sw_raw,sw_d]) sw_hash_rows \<and>
        list_all sw_external_rows sw_issuer_facts
     then map (map integer_of_nat)
       (sw_phase_integer (map (map nat_of_integer) sw_rows)
          (map (\<lambda>(sw_id,sw_key). (nat_of_integer sw_id, map nat_of_integer sw_key)) sw_signers)
          (map (map nat_of_integer) sw_good_keys)
          (map (\<lambda>(sw_raw,sw_d). (map nat_of_integer sw_raw,map nat_of_integer sw_d)) sw_hash_rows)
          (map (map (map nat_of_integer)) sw_issuer_facts))
     else [[0]])"

export_code sw_observe_integer
  in SML module_name OIP_Source_Writer_Integer_ABI file_prefix "oip_source_writer_integer_abi"

end
