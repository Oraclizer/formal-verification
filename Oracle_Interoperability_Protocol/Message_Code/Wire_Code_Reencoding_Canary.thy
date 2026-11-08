theory Wire_Code_Reencoding_Canary
  imports Wire_Code_Encoder "OIP_Product.Wire_Byte_Examples"
begin

text \<open>
  Feasibility witnesses are kept outside the production theory ancestry.
  The mutation below removes only the exact re-encoding comparison while
  keeping parsing, encoder success, and the typed canonical core unchanged.
\<close>

definition model_checked_core_encoder where
  "model_checked_core_encoder core = code_typed_encode_core core"

lemma the_canary_encoder_is_the_source_encoder_function:
  "model_checked_core_encoder = code_typed_encode_core"
  by (rule ext) (simp only: model_checked_core_encoder_def)

lemma the_canary_encoder_meets_the_explicit_encoder_obligation:
  "code_core_encoder_sound model_checked_core_encoder"
  by (simp only: the_canary_encoder_is_the_source_encoder_function
    the_typed_source_core_encoder_discharges_the_reencoding_obligation)

lemma a_typed_canonical_core_passes_the_actual_reencoding_consumer:
  "code_reencoding_decode (\<lambda>_. True) (\<lambda>_. Some wire_case_core)
    model_checked_core_encoder wire_case_exact_core_bytes = Some wire_case_core"
  by (simp add: code_reencoding_decode_def model_checked_core_encoder_def
    the_typed_source_encoder_is_the_checked_canonical_encoder
    wire_case_core_is_wellformed concrete_protobuf_query_has_the_exact_canonical_core)

lemma a_different_byte_string_does_not_pass_the_reencoding_consumer:
  "code_reencoding_decode (\<lambda>_. True) (\<lambda>_. Some wire_case_core)
    model_checked_core_encoder [] = None"
  by (simp add: code_reencoding_decode_def model_checked_core_encoder_def
    the_typed_source_encoder_is_the_checked_canonical_encoder
    wire_case_core_is_wellformed concrete_protobuf_query_has_the_exact_canonical_core
    wire_case_exact_core_bytes_def)

definition code_decode_without_exact_comparison where
  "code_decode_without_exact_comparison shape parse encode bytes =
    (if \<not> shape bytes then None
     else case parse bytes of None \<Rightarrow> None | Some value \<Rightarrow>
       (case encode value of None \<Rightarrow> None | Some canonical \<Rightarrow> Some value))"

lemma removing_the_comparison_reaches_a_false_semantic_acceptance:
  "code_decode_without_exact_comparison (\<lambda>_. True) (\<lambda>_. Some wire_case_core)
      model_checked_core_encoder [] = Some wire_case_core"
  "encode_wire_core wire_case_core \<noteq> []"
  "decode_wire_core [] \<noteq> Some wire_case_core"
proof -
  show "code_decode_without_exact_comparison (\<lambda>_. True) (\<lambda>_. Some wire_case_core)
      model_checked_core_encoder [] = Some wire_case_core"
    by (simp add: code_decode_without_exact_comparison_def model_checked_core_encoder_def
      the_typed_source_encoder_is_the_checked_canonical_encoder
      wire_case_core_is_wellformed)
  show nonempty: "encode_wire_core wire_case_core \<noteq> []"
    by (simp add: concrete_protobuf_query_has_the_exact_canonical_core wire_case_exact_core_bytes_def)
  show "decode_wire_core [] \<noteq> Some wire_case_core"
    using accepted_core_bytes_preserve_all_original_fields[of "[]" wire_case_core] nonempty by blast
qed

end
