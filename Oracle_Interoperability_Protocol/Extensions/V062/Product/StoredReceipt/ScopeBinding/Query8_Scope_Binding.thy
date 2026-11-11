theory Query8_Scope_Binding
  imports "OIP_Exact_Receipt_Core_Comparison.Exact_Receipt_Core_Comparison"
begin

text \<open>The selected record supplies exact stored Core bytes. This leaf
decodes every supplied Core and derives its transport key. The record
selection, token trust policy, durable receipt, and subsequent publication
are outside this interface. The only supported receipt original is Write.\<close>

fun q8_scope_slots :: "wire_bytes list \<Rightarrow> (authenticated_message_id \<times> wire_bytes) list option" where
  "q8_scope_slots [] = Some []"
| "q8_scope_slots (saved # remaining) =
    Option.bind (decode_wire_core saved) (\<lambda>core.
      Option.bind (q8_scope_slots remaining) (\<lambda>slots.
        let key = code_transport_key core in
        if map_of slots key \<noteq> None then None else Some ((key,saved) # slots)))"

fun q8_arrival_tag where
  "q8_arrival_tag Code_First = (0::nat)"
| "q8_arrival_tag Code_Identical = 1"
| "q8_arrival_tag Code_Replay_Conflict = 2"

fun q8_nested_status where
  "q8_nested_status Code_First = (50::nat)"
| "q8_nested_status Code_Identical = 0"
| "q8_nested_status Code_Replay_Conflict = 76"

text \<open>Words are status, outer checked, outer comparison, context checked,
context equal, inner checked, inner comparison. Status 0 means entry to the
receipt consumer is eligible. It does not encode a returned receipt.\<close>

definition q8_scope_select where
  "q8_scope_select check_context slots outer original =
    (let outer_arrival = code_compare_binding (map_of slots (code_transport_key outer)) (encode_wire_core outer)
     in case outer_arrival of Code_Replay_Conflict \<Rightarrow> [76,1,2,0,0,0,0]
     | _ \<Rightarrow>
       (let same = code_same_original outer original; outer_tag = q8_arrival_tag outer_arrival in
        if check_context \<and> \<not> same then [72,1,outer_tag,1,0,0,0]
        else let inner_arrival = code_compare_binding (map_of slots (code_transport_key original)) (encode_wire_core original)
          in [q8_nested_status inner_arrival,1,outer_tag,1,(if same then 1 else 0),1,q8_arrival_tag inner_arrival]))"

lemma q8_a_decoded_single_slot_preserves_its_exact_bytes:
  assumes "decode_wire_core saved = Some stored"
  shows "q8_scope_slots [saved] = Some [(code_transport_key stored,saved)]"
  using assms by (simp add: Let_def)

lemma q8_single_slot_reuses_the_checked_core_comparison:
  assumes stored: "decode_wire_core saved = Some stored" and original: "decode_wire_core raw = Some original"
  shows "exact_receipt_core_comparison saved raw =
    Some (code_ir_transport_key stored,code_ir_transport_key original,
      q8_arrival_tag
        (code_compare_binding (map_of [(code_transport_key stored,saved)] (code_transport_key original)) raw))"
proof -
  have previous: "exact_receipt_core_comparison saved raw =
    Some (code_ir_transport_key stored,code_ir_transport_key original,
      if authenticated_wire_message_id stored \<noteq> authenticated_wire_message_id original then 0
      else if saved = raw then 1 else 2)"
    by (rule the_supplied_receipt_slot_compares_the_decoded_key_and_exact_original_bytes[OF assms])
  have same_raw: "saved = raw \<Longrightarrow> stored = original"
    using stored original by simp
  have classification: "q8_arrival_tag
        (code_compare_binding (map_of [(code_transport_key stored,saved)] (code_transport_key original)) raw) =
      (if authenticated_wire_message_id stored \<noteq> authenticated_wire_message_id original then 0
       else if saved = raw then 1 else 2)"
  proof (cases "authenticated_wire_message_id stored = authenticated_wire_message_id original")
    case True
    then show ?thesis
      by (cases "saved = raw") (simp_all add: code_compare_binding_def
        the_source_transport_key_has_the_exact_authenticated_model_components)
  next
    case False
    have "saved \<noteq> raw" using False same_raw by blast
    with False show ?thesis
      by (simp add: code_compare_binding_def the_source_transport_key_has_the_exact_authenticated_model_components)
  qed
  show ?thesis using previous by (simp only: classification)
qed

lemma q8_outer_conflict_stops_before_the_original_context:
  assumes "code_compare_binding (map_of slots (code_transport_key outer))
    (encode_wire_core outer) = Code_Replay_Conflict"
  shows "q8_scope_select check_context slots outer original = [76,1,2,0,0,0,0]"
  using assms by (simp add: q8_scope_select_def Let_def)

lemma q8_removing_only_context_changes_a_foreign_missing_original:
  assumes outer: "code_compare_binding (map_of slots (code_transport_key outer))
                    (encode_wire_core outer) = Code_First"
    and foreign: "\<not> code_same_original outer original"
    and missing: "map_of slots (code_transport_key original) = None"
  shows "q8_scope_select True slots outer original = [72,1,0,1,0,0,0]"
    and "q8_scope_select False slots outer original = [50,1,0,1,0,1,0]"
proof -
  have first: "code_compare_binding (map_of slots (code_transport_key original))
      (encode_wire_core original) = Code_First"
    using missing by (simp add: code_compare_binding_def)
  show "q8_scope_select True slots outer original = [72,1,0,1,0,0,0]"
    using outer foreign by (simp add: q8_scope_select_def Let_def)
  show "q8_scope_select False slots outer original = [50,1,0,1,0,1,0]"
    using outer foreign first by (simp add: q8_scope_select_def Let_def)
qed

lemma q8_same_context_distinguishes_all_three_inner_comparisons:
  assumes outer: "code_compare_binding (map_of slots (code_transport_key outer))
                    (encode_wire_core outer) = Code_First"
    and same: "code_same_original outer original"
  shows "q8_scope_select True slots outer original =
    (let inner = code_compare_binding (map_of slots (code_transport_key original)) (encode_wire_core original)
     in [q8_nested_status inner,1,0,1,1,1,q8_arrival_tag inner])"
  using outer same by (simp add: q8_scope_select_def Let_def)

definition q8_scope_stop where
  "q8_scope_stop status = [[status,0,0,0,0,0,0],[],[],[],[]]"

definition q8_scope_view where
  "q8_scope_view decision outer original =
    [decision,code_ir_transport_key outer,code_ir_transport_key original,
     encode_wire_core outer,encode_wire_core original]"

definition q8_scope_receipt where
  "q8_scope_receipt check_context slots fuel token_verified identity outer =
    (case code_decode_operand_tree fuel outer of
       Code_Tree_Refused reason \<Rightarrow> Some (q8_scope_stop (code_transport_refusal_number reason))
     | Code_Tree_Ready (Code_Nested_Receipt original) \<Rightarrow>
       (if wire_message_family original \<noteq> Wire_Lock \<or> wire_opcode (wire_operation_body original) \<noteq> 7 then None
        else case wire_words (wire_operation_body outer) of [session] \<Rightarrow>
          if token_verified \<and>
             identity = [wire_deployment outer,wire_authority_epoch outer,session,wire_source_domain outer,wire_principal outer]
          then Some (q8_scope_view (q8_scope_select check_context slots outer original) outer original)
          else Some (q8_scope_stop 72)
        | _ \<Rightarrow> Some (q8_scope_stop 70))
     | _ \<Rightarrow> None)"

definition q8_scope_packet where
  "q8_scope_packet check_context authority fuel signature_verified token_verified identity preimage signature slots bytes =
    (case code_check_declared_version bytes (boundary_max_frame authority) of
       Some reason \<Rightarrow> Some (q8_scope_stop (code_transport_refusal_number reason))
     | None \<Rightarrow>
       (case decode_wire_packet bytes of None \<Rightarrow> Some (q8_scope_stop 70)
        | Some packet \<Rightarrow>
          (case code_admit_packet (\<lambda>_ message supplied. signature_verified \<and> message = preimage \<and> supplied = signature)
                   packet authority of
             Some reason \<Rightarrow> Some (q8_scope_stop (code_transport_refusal_number reason))
           | None \<Rightarrow> q8_scope_receipt check_context slots fuel token_verified identity (packet_core packet))))"

definition q8_scope_integer ::
  "bool \<Rightarrow> integer list \<Rightarrow> integer list list \<Rightarrow> integer list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow>
    integer list \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow>
    integer list \<Rightarrow> integer list \<Rightarrow> integer list list option" where
  "q8_scope_integer check_context bytes stored values version families atomicities schemes critical
       signature_verified token_verified identity preimage signature =
    (if length values = 13 \<and> length identity = 5 \<and> version = 6 \<and> schemes = [1] \<and>
        code_integer_u64_values (values @ identity @ [version] @ families @ atomicities @ schemes) \<and>
        code_integer_common_host_values values \<and> list_all code_integer_octet_values (bytes # preimage # signature # stored)
     then Option.bind (q8_scope_slots (map (map nat_of_integer) stored)) (\<lambda>slots.
       map_option (map (map integer_of_nat))
         (q8_scope_packet check_context
           (code_contract_boundary (map nat_of_integer values) (nat_of_integer version)
             (map nat_of_integer families) (map nat_of_integer atomicities) (map nat_of_integer schemes) critical)
           (nat_of_integer (values ! 12)) signature_verified token_verified (map nat_of_integer identity)
           (map nat_of_integer preimage) (map nat_of_integer signature) slots (map nat_of_integer bytes)))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      q8_a_decoded_single_slot_preserves_its_exact_bytes
      q8_single_slot_reuses_the_checked_core_comparison
      q8_outer_conflict_stops_before_the_original_context
      q8_removing_only_context_changes_a_foreign_missing_original
      q8_same_context_distinguishes_all_three_inner_comparisons
      accepted_core_bytes_preserve_all_original_fields
      a_conflicting_retained_core_is_never_overwritten})
  then () else error "Unexpected oracle in Query8 scope and binding leaf"
\<close>

export_code q8_scope_integer
  in SML module_name OIP_Query8_Scope_ABI file_prefix "oip_query8_scope_abi"

end
