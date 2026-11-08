theory Recovery_Reply_Table_Insertions
  imports "OIP_Product.Recovery_Service"
begin

text \<open>These helpers concern actual retained receipt maps. Fresh pre-state entries are operational
  facts derived from the producer, not assumed reply agreement.\<close>

lemma equal_fresh_single_insertions_identify_the_same_key_and_value:
  assumes fresh_a: "table key_a = None"
    and fresh_b: "table key_b = None"
    and same: "table(key_a := Some value_a) = table(key_b := Some value_b)"
  shows "key_a = key_b" "value_a = value_b"
proof -
  have at_a: "(table(key_a := Some value_a)) key_a = (table(key_b := Some value_b)) key_a"
    by (rule fun_cong[OF same])
  show keys: "key_a = key_b" using fresh_a at_a by (cases "key_a = key_b") auto
  show "value_a = value_b" using at_a keys by simp
qed

lemma equal_insertions_over_equal_base_tables_identify_the_value:
  assumes bases: "before_a = before_b"
    and fresh_a: "before_a key_a = None"
    and fresh_b: "before_b key_b = None"
    and same: "before_a(key_a := Some value_a) = before_b(key_b := Some value_b)"
  shows "value_a = value_b"
proof -
  have second_fresh: "before_a key_b = None" using bases fresh_b by simp
  have updates: "before_a(key_a := Some value_a) = before_a(key_b := Some value_b)"
    using bases same by simp
  show ?thesis by (rule equal_fresh_single_insertions_identify_the_same_key_and_value(2)
    [OF fresh_a second_fresh updates])
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms equal_fresh_single_insertions_identify_the_same_key_and_value
      equal_insertions_over_equal_base_tables_identify_the_value})
  then () else error "Unexpected oracle in retained reply table helper"
\<close>

end
