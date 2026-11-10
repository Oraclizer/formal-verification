theory Sync_V061_Direct_IR
  imports "OIP_Sync_V061_Position_Definitions.Sync_V061_Product"
    "OIP_Message_Code.Wire_Code_Typed_Summary_Check"
begin

fun sync_mode_number :: "sync_mode \<Rightarrow> nat" where
  "sync_mode_number Sync_Initial = 1"
| "sync_mode_number Sync_Incremental = 2"
| "sync_mode_number Sync_Full = 3"

definition sync_call_operand_ir where
  "sync_call_operand_ir request = (let item = sync_requested request; stream = sync_key request in
    code_ir_node 22 [code_ir_scalar (sync_message request),code_ir_pair (sync_call request),
      code_ir_scalar (sync_session request),code_ir_cut (sync_signed_cut request),
      code_ir_scalar (sync_origin_epoch item),code_ir_pair (snd stream,sync_event item),
      code_ir_scalar (fst stream),code_ir_scalar (sync_position item),code_ir_scalar (sync_mode_number (sync_mode request)),
      code_ir_bytes (sync_commitment item),code_ir_option code_ir_bytes (sync_claimed_prior request),
      code_ir_bytes (sync_attestation request)])"

definition sync_query_operand_ir where
  "sync_query_operand_ir request = (let cut = sync_query_cut request; stream = sync_query_key request in
    code_ir_node 13 [
      code_ir_node 104 [code_ir_scalar (sync_query_session request),code_ir_scalar (cut_authority_epoch cut)],
      code_ir_node 156 [code_ir_cut cut,code_ir_scalar (fst stream),code_ir_scalar (snd stream)]])"

definition sync_direct_operand_ir :: "nat \<Rightarrow> wire_core \<Rightarrow> nat list option" where
  "sync_direct_operand_ir depth core =
    (if depth = 0 then None else if sync_operation core = (Wire_State_Sync,7) then
       map_option sync_call_operand_ir (sync_read_operands core)
     else map_option sync_query_operand_ir (sync_read_query core))"

lemma sync_direct_operand_is_the_new_decoded_value:
  assumes "sync_direct_operand_ir depth core = Some result"
  shows "depth > 0"
    "(sync_operation core = (Wire_State_Sync,7) \<and>
       (\<exists>request. sync_read_operands core = Some request \<and> result = sync_call_operand_ir request)) \<or>
     (sync_operation core = (Wire_Query,9) \<and>
       (\<exists>request. sync_read_query core = Some request \<and> result = sync_query_operand_ir request))"
proof -
  have nonzero: "depth \<noteq> 0"
  proof
    assume "depth = 0"
    with assms show False by (simp add: sync_direct_operand_ir_def)
  qed
  show "depth > 0" using nonzero by simp
  show "(sync_operation core = (Wire_State_Sync,7) \<and>
           (\<exists>request. sync_read_operands core = Some request \<and> result = sync_call_operand_ir request)) \<or>
        (sync_operation core = (Wire_Query,9) \<and>
           (\<exists>request. sync_read_query core = Some request \<and> result = sync_query_operand_ir request))"
  proof (cases "sync_operation core = (Wire_State_Sync,7)")
    case True
    with assms nonzero obtain request where "sync_read_operands core = Some request"
      "result = sync_call_operand_ir request"
      by (auto simp: sync_direct_operand_ir_def map_option_eq_Some)
    then show ?thesis using True by blast
  next
    case False
    with assms nonzero obtain request where query: "sync_read_query core = Some request"
      "result = sync_query_operand_ir request"
      by (auto simp: sync_direct_operand_ir_def map_option_eq_Some)
    have "sync_operation core = (Wire_Query,9)"
      using query(1) by (auto simp: sync_read_query_def Let_def split: if_splits)
    then show ?thesis using query by blast
  qed
qed

lemma sync_direct_opaque_proof_appears_in_its_exact_ir_field:
  "sync_call_operand_ir request = code_ir_node 22
    [code_ir_scalar (sync_message request),code_ir_pair (sync_call request),
      code_ir_scalar (sync_session request),code_ir_cut (sync_signed_cut request),
      code_ir_scalar (sync_origin_epoch (sync_requested request)),
      code_ir_pair (snd (sync_key request),sync_event (sync_requested request)),
      code_ir_scalar (fst (sync_key request)),code_ir_scalar (sync_position (sync_requested request)),
      code_ir_scalar (sync_mode_number (sync_mode request)),code_ir_bytes (sync_commitment (sync_requested request)),
      code_ir_option code_ir_bytes (sync_claimed_prior request),code_ir_bytes (sync_attestation request)]"
  by (simp add: sync_call_operand_ir_def Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_direct_operand_is_the_new_decoded_value
    sync_direct_opaque_proof_appears_in_its_exact_ir_field})
  then () else error "Unexpected oracle in the synchronization typed operand projection"
\<close>

end
