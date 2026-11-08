theory Wire_Code_Typed_IR
  imports Wire_Code_Oracle_Codegen Wire_Code_Fixed_Call_Request
begin

definition code_ir_scalar :: "nat \<Rightarrow> nat list" where
  "code_ir_scalar oip_binder_value = [0,oip_binder_value]"

definition code_ir_bytes :: "wire_bytes \<Rightarrow> nat list" where
  "code_ir_bytes oip_binder_bytes = [1,length oip_binder_bytes] @ oip_binder_bytes"

definition code_ir_list :: "('a \<Rightarrow> nat list) \<Rightarrow> 'a list \<Rightarrow> nat list" where
  "code_ir_list oip_binder_render oip_binder_values = [2,length oip_binder_values] @ concat (map oip_binder_render oip_binder_values)"

fun code_ir_option :: "('a \<Rightarrow> nat list) \<Rightarrow> 'a option \<Rightarrow> nat list" where
  "code_ir_option oip_binder_render None = [3]"
| "code_ir_option oip_binder_render (Some oip_binder_value) = 4 # oip_binder_render oip_binder_value"

definition code_ir_node :: "nat \<Rightarrow> nat list list \<Rightarrow> nat list" where
  "code_ir_node = (\<lambda>oip_binder_tag oip_binder_field_chunks. [oip_binder_tag,length oip_binder_field_chunks] @ concat oip_binder_field_chunks)"

definition code_ir_pair :: "(nat \<times> nat) \<Rightarrow> nat list" where
  "code_ir_pair oip_binder_pair = code_ir_node 90 [code_ir_scalar (fst oip_binder_pair),code_ir_scalar (snd oip_binder_pair)]"

definition code_ir_triple :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat list" where
  "code_ir_triple oip_binder_triple = (case oip_binder_triple of (oip_binder_first,oip_binder_second,oip_binder_third) \<Rightarrow>
    code_ir_node 91 [code_ir_scalar oip_binder_first,code_ir_scalar oip_binder_second,code_ir_scalar oip_binder_third])"

definition code_ir_set :: "nat set \<Rightarrow> nat list" where
  "code_ir_set oip_binder_values = code_ir_list code_ir_scalar (sorted_list_of_set oip_binder_values)"

definition code_ir_cut :: "product_cut \<Rightarrow> nat list" where
  "code_ir_cut = (\<lambda>oip_binder_selected_cut. code_ir_pair (cut_authority_epoch oip_binder_selected_cut,cut_revision oip_binder_selected_cut))"

lemma the_typed_ir_scalar_preserves_the_entire_integer:
  fixes oip_binder_first oip_binder_second :: nat
  shows "code_ir_scalar oip_binder_first = code_ir_scalar oip_binder_second \<longleftrightarrow> oip_binder_first = oip_binder_second"
  by (simp add: code_ir_scalar_def)

lemma the_typed_ir_byte_node_preserves_its_entire_typed_field:
  fixes oip_binder_first oip_binder_second :: wire_bytes
  shows "code_ir_bytes oip_binder_first = code_ir_bytes oip_binder_second \<longleftrightarrow> oip_binder_first = oip_binder_second"
proof
  assume same_bytes: "code_ir_bytes oip_binder_first = code_ir_bytes oip_binder_second"
  then show "oip_binder_first = oip_binder_second"
    by (auto simp: code_ir_bytes_def)
next
  assume same_value: "oip_binder_first = oip_binder_second"
  then show "code_ir_bytes oip_binder_first = code_ir_bytes oip_binder_second" by simp
qed

lemma a_typed_ir_domain_constructor_keeps_its_tag_and_arity:
  fixes oip_binder_tag :: nat and oip_binder_field_chunks :: "nat list list"
  shows "take 2 (code_ir_node oip_binder_tag oip_binder_field_chunks) = [oip_binder_tag,length oip_binder_field_chunks]"
  by (simp add: code_ir_node_def)

lemma a_decoded_finite_set_has_an_executable_canonical_order:
  fixes oip_binder_values :: "nat list"
  shows "code_ir_set (set oip_binder_values) = code_ir_list code_ir_scalar (sort (remdups oip_binder_values))"
  by (simp add: code_ir_set_def sorted_list_of_set_sort_remdups)

text \<open>
  This is the new typed observation interface. No existing datatype,
  decoder, acceptance predicate or code equation is changed. Byte fields
  below are actual typed proof fields or canonical encodings of a decoded
  OriginalCore, never a substitute for its recursive typed operand.
  Finite decoded sets use the standard sorted_list_of_set code equation
  on their set-of-list producer; no nat enumeration is introduced.
\<close>

end
