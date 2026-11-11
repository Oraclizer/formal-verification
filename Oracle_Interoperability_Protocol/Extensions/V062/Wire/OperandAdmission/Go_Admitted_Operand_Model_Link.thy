theory Go_Admitted_Operand_Model_Link
  imports "OIP_Message_Code.Wire_Code_Typed_Summary_Check"
begin

definition gao_packet_operand_rows ::
  "wire_bytes \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "gao_packet_operand_rows gao_bytes gao_max_frame gao_max_nesting =
    (let gao_version = code_check_declared_version gao_bytes gao_max_frame;
         gao_declared = (case code_declared_version gao_bytes of
           None \<Rightarrow> [] | Some gao_number \<Rightarrow> [gao_number]);
         gao_precheck = (case gao_version of None \<Rightarrow> [1]
           | Some gao_reason \<Rightarrow> [2,code_transport_refusal_number gao_reason])
     in [gao_declared,gao_precheck] @
       (case gao_version of Some _ \<Rightarrow> [[0],[0],[],[],[]]
        | None \<Rightarrow>
          (case decode_wire_packet gao_bytes of
             None \<Rightarrow> [[2,code_transport_refusal_number Invalid_Wire_Format],[0],[],[],[]]
           | Some gao_packet \<Rightarrow>
             let gao_core = packet_core gao_packet; gao_exact = encode_wire_core gao_core in
             (case code_decode_operand_tree gao_max_nesting gao_core of
                Code_Tree_Refused gao_reason \<Rightarrow>
                  [[1],[2,code_transport_refusal_number gao_reason],gao_exact,[],[]]
              | Code_Tree_Pending \<Rightarrow> [[1],[3],gao_exact,[],[]]
              | Code_Tree_Ready _ \<Rightarrow>
                (case code_typed_operand_ir gao_max_nesting gao_core of
                   None \<Rightarrow> [[1],[4],gao_exact,[],[]]
                 | Some gao_ir \<Rightarrow> [[1],[1],gao_exact,gao_ir,gao_exact])))))"

lemma gao_outer_refusal_skips_operand:
  assumes "code_check_declared_version gao_bytes gao_max_frame = None"
    "decode_wire_packet gao_bytes = None"
  shows "drop 2 (gao_packet_operand_rows gao_bytes gao_max_frame gao_max_nesting) =
    [[2,code_transport_refusal_number Invalid_Wire_Format],[0],[],[],[]]"
  using assms by (simp add: gao_packet_operand_rows_def Let_def)

lemma gao_operand_refusal_keeps_the_decoded_core:
  assumes "code_check_declared_version gao_bytes gao_max_frame = None"
    "decode_wire_packet gao_bytes = Some gao_packet"
    "code_decode_operand_tree gao_max_nesting (packet_core gao_packet) = Code_Tree_Refused gao_reason"
  shows "drop 2 (gao_packet_operand_rows gao_bytes gao_max_frame gao_max_nesting) =
    [[1],[2,code_transport_refusal_number gao_reason],encode_wire_core (packet_core gao_packet),[],[]]"
  using assms by (simp add: gao_packet_operand_rows_def Let_def)

lemma gao_success_exposes_the_typed_ir_and_its_exact_core:
  assumes "code_check_declared_version gao_bytes gao_max_frame = None"
    "decode_wire_packet gao_bytes = Some gao_packet"
    "code_decode_operand_tree gao_max_nesting (packet_core gao_packet) = Code_Tree_Ready gao_operand"
    "code_typed_operand_ir gao_max_nesting (packet_core gao_packet) = Some gao_ir"
  shows "drop 2 (gao_packet_operand_rows gao_bytes gao_max_frame gao_max_nesting) =
    [[1],[1],encode_wire_core (packet_core gao_packet),gao_ir,encode_wire_core (packet_core gao_packet)]"
  using assms by (simp add: gao_packet_operand_rows_def Let_def)

definition gao_u64 :: "integer \<Rightarrow> bool" where
  "gao_u64 gao_number \<longleftrightarrow> 0 \<le> gao_number \<and> gao_number < 18446744073709551616"

definition gao_integer_abi :: "integer list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer list list option" where
  "gao_integer_abi gao_bytes gao_max_frame gao_max_nesting =
    (if gao_u64 gao_max_frame \<and> gao_u64 gao_max_nesting
        \<and> list_all (\<lambda>gao_byte. 0 \<le> gao_byte \<and> gao_byte < 256) gao_bytes
     then Some (map (map integer_of_nat)
       (gao_packet_operand_rows (map nat_of_integer gao_bytes)
         (nat_of_integer gao_max_frame) (nat_of_integer gao_max_nesting)))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms gao_outer_refusal_skips_operand
      gao_operand_refusal_keeps_the_decoded_core gao_success_exposes_the_typed_ir_and_its_exact_core
      code_decode_operand_tree_integer_code code_typed_operand_ir_integer_code})
  then () else error "Unexpected oracle in Go packet operand link"
\<close>

export_code gao_integer_abi in SML
  module_name OIP_Go_Admitted_Operand_Link file_prefix "oip_go_admitted_operand_link"

end
