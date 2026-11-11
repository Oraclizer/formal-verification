theory Source_Writer_JSON_G0
  imports "OIP_Message_Code.Wire_Code_JSON_Primitives" "HOL-Library.Code_Target_Nat"
begin

text \<open>Compact JSON of the first decision only. The field order is the
  declared Rust Serialize order, and empty commitments and absent
  commitment_authorities have no JSON key. The byte equality is checked
  separately on the two frozen native input chains.\<close>

type_synonym sw_json_bytes = "nat list"
type_synonym sw_json_mark = "nat \<times> sw_json_bytes"
type_synonym sw_json_profile = "nat \<times> nat \<times> nat"

fun sw_decimal_fuel :: "nat \<Rightarrow> nat \<Rightarrow> sw_json_bytes" where
  "sw_decimal_fuel 0 sw_n = []"
| "sw_decimal_fuel (Suc sw_fuel) sw_n =
    (if sw_n < 10 then [48 + sw_n]
     else sw_decimal_fuel sw_fuel (sw_n div 10) @ [48 + sw_n mod 10])"

definition sw_decimal :: "nat \<Rightarrow> sw_json_bytes" where
  "sw_decimal sw_n = sw_decimal_fuel 20 sw_n"

fun sw_json_elements :: "sw_json_bytes list \<Rightarrow> sw_json_bytes" where
  "sw_json_elements [] = []"
| "sw_json_elements (sw_item # sw_rest) =
     sw_item @ (if sw_rest = [] then [] else [44] @ sw_json_elements sw_rest)"

definition sw_json_array :: "sw_json_bytes list \<Rightarrow> sw_json_bytes" where
  "sw_json_array sw_items = [91] @ sw_json_elements sw_items @ [93]"

definition sw_json_octets :: "sw_json_bytes \<Rightarrow> sw_json_bytes" where
  "sw_json_octets sw_bytes = sw_json_array (map sw_decimal sw_bytes)"

definition sw_profile_json :: "sw_json_profile \<Rightarrow> sw_json_bytes" where
  "sw_profile_json sw_cfg = (case sw_cfg of (sw_deploy,sw_format,sw_authority) \<Rightarrow>
     code_json_open_key ''deployment'' @ sw_decimal sw_deploy @
     code_json_next_key ''format'' @ sw_decimal sw_format @
     code_json_next_key ''authority_profile'' @ sw_decimal sw_authority @ [125])"

definition sw_stores_json where
  "sw_stores_json sw_journal sw_witness sw_rules =
     code_json_open_key ''journal'' @ sw_json_octets sw_journal @
     code_json_next_key ''witness'' @ sw_json_octets sw_witness @
     code_json_next_key ''authorities'' @ sw_json_octets sw_rules @ [125]"

definition sw_mark_json :: "sw_json_mark \<Rightarrow> sw_json_bytes" where
  "sw_mark_json sw_m =
     code_json_open_key ''revision'' @ sw_decimal (fst sw_m) @
     code_json_next_key ''sha256'' @ sw_json_octets (snd sw_m) @ [125]"

definition sw_encoding_bound :: sw_json_mark where
  "sw_encoding_bound = (2^64 - 1, replicate 32 255)"

definition sw_state_json where
  "sw_state_json sw_cfg sw_stores sw_prep sw_decisions =
     code_json_open_key ''profile'' @ sw_profile_json sw_cfg @
     code_json_next_key ''stores'' @ sw_stores @
     code_json_next_key ''preparation'' @
       (case sw_prep of None \<Rightarrow> code_json_ascii ''null'' | Some sw_m \<Rightarrow> sw_mark_json sw_m) @
     code_json_next_key ''decisions'' @ sw_json_array sw_decisions @ [125]"

definition sw_selected_body_json where
  "sw_selected_body_json sw_state sw_m =
     code_json_open_key ''state'' @ sw_state @
     code_json_next_key ''journal'' @ sw_mark_json sw_m @ [125]"

definition sw_selected_json where
  "sw_selected_json sw_state sw_m =
     code_json_open_key ''Selected'' @ sw_selected_body_json sw_state sw_m @ [125]"

definition sw_initializing_json where
  "sw_initializing_json sw_state sw_m =
     code_json_open_key ''Initializing'' @
     code_json_open_key ''state'' @ sw_state @
     code_json_next_key ''empty_journal'' @ sw_mark_json sw_m @ [125,125]"

definition sw_appending_json where
  "sw_appending_json sw_state sw_m sw_decision =
     code_json_open_key ''Appending'' @
     code_json_open_key ''before'' @ sw_selected_body_json sw_state sw_m @
     code_json_next_key ''decision'' @ sw_decision @ [125,125]"

definition sw_repairing_json where
  "sw_repairing_json sw_state sw_m sw_observed =
     code_json_open_key ''Repairing'' @
     code_json_open_key ''selected'' @ sw_selected_body_json sw_state sw_m @
     code_json_next_key ''observed_journal'' @ sw_mark_json sw_observed @ [125,125]"

lemma sw_g0_decimal_widths:
  "map sw_decimal [0,9,10,99,100,255,4294967295,18446744073709551615] =
    map code_json_ascii [''0'',''9'',''10'',''99'',''100'',''255'',''4294967295'',''18446744073709551615'']"
  by code_simp

lemma sw_g0_bound_mark:
  "sw_encoding_bound = (18446744073709551615, replicate 32 255)"
  by code_simp

lemma sw_g0_profile_order:
  "sw_profile_json (0,4294967295,18446744073709551615) =
    [123,34] @ code_json_ascii ''deployment'' @ [34,58,48,44,34] @
    code_json_ascii ''format'' @ [34,58] @ code_json_ascii ''4294967295'' @ [44,34] @
    code_json_ascii ''authority_profile'' @ [34,58] @ code_json_ascii ''18446744073709551615'' @ [125]"
  by code_simp

lemma sw_g0_bound_mark_length:
  "length (sw_mark_json sw_encoding_bound) = 172"
  by code_simp

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sw_g0_decimal_widths sw_g0_bound_mark sw_g0_profile_order sw_g0_bound_mark_length})
  then () else error "Unexpected oracle in source writer JSON G0"
\<close>

end
