theory Sync_V061_Reference_Boundary
  imports "OIP_Sync_V061_Position_Originals.Sync_V061_Originals"
begin

record sync_reference_gate =
  sync_endpoint_up :: bool
  sync_source_connected :: bool
  sync_registered_asset :: "product_asset \<Rightarrow> bool"
  sync_other_claimed :: "client_call_id \<Rightarrow> bool"
  sync_ordered_debit :: "client_call_id \<Rightarrow> bool"
  sync_receipt_granted :: "product_session_id \<Rightarrow> product_asset \<Rightarrow> bool"

datatype sync_reference_result =
  Sync_Transport_Refusal wire_refusal | Sync_Product_Refusal | Sync_Reference_Outcome sync_outcome

definition sync_reference_product where
  "sync_reference_product transport gate verify core state =
    (case transport of Some refusal \<Rightarrow> (state, Sync_Transport_Refusal refusal)
     | None \<Rightarrow> (case sync_read_operands core of
         None \<Rightarrow> (state, Sync_Transport_Refusal Invalid_Wire_Format)
       | Some request \<Rightarrow>
         let id = sync_call request; asset = fst (sync_key request);
             original = sync_outcome_table state id;
             refusal = (state, Sync_Product_Refusal)
         in if sync_ordered_debit gate id then (state, Sync_Transport_Refusal Conflicting_Wire_Replay)
         else if \<not> sync_execute_allowed state core request \<or> \<not> sync_endpoint_up gate then refusal
         else case original of
           Some (exact,outcome) \<Rightarrow>
             if sync_receipt_granted gate (sync_session request) asset \<and> exact = encode_wire_core core
             then (state, Sync_Reference_Outcome outcome) else refusal
         | None \<Rightarrow>
             if sync_other_claimed gate id \<or> \<not> sync_registered_asset gate asset then refusal
             else let assessed = if sync_source_connected gate
                                then sync_fresh_assess verify state core request
                                else Sync_Reject Sync_Unavailable
                  in case assessed of
                    Sync_Reject reason \<Rightarrow>
                      (sync_write_outcome state core request (Sync_Uncommitted reason),
                       Sync_Reference_Outcome (Sync_Uncommitted reason))
                  | Sync_Accept statement \<Rightarrow>
                      if 2^64 - 1 \<le> cut_revision (sync_current_cut state) then refusal
                      else (sync_commit_record state core request statement,
                            Sync_Reference_Outcome (Sync_Committed (cut_revision (sync_current_cut state))))))"

lemma sync_reference_transport_refusal_precedes_product:
  "sync_reference_product (Some refusal) gate verify core state = (state, Sync_Transport_Refusal refusal)"
  by (simp add: sync_reference_product_def)

lemma sync_reference_reserved_debit_id_refuses_before_execution:
  assumes "sync_read_operands core = Some request" "sync_ordered_debit gate (sync_call request)"
  shows "sync_reference_product None gate verify core state = (state, Sync_Transport_Refusal Conflicting_Wire_Replay)"
  using assms by (simp add: sync_reference_product_def Let_def)

lemma sync_reference_exact_retry_requires_current_execution_and_receipt:
  assumes "sync_read_operands core = Some request" "\<not> sync_ordered_debit gate (sync_call request)"
    "sync_outcome_table state (sync_call request) = Some (exact,outcome)"
  shows "sync_reference_product None gate verify core state =
    (if sync_execute_allowed state core request \<and> sync_endpoint_up gate \<and>
        sync_receipt_granted gate (sync_session request) (fst (sync_key request)) \<and> exact = encode_wire_core core
     then (state, Sync_Reference_Outcome outcome) else (state, Sync_Product_Refusal))"
  using assms by (auto simp: sync_reference_product_def Let_def)

lemma sync_reference_other_call_collision_is_refused_without_record:
  assumes "sync_read_operands core = Some request" "\<not> sync_ordered_debit gate (sync_call request)"
    "sync_outcome_table state (sync_call request) = None" "sync_other_claimed gate (sync_call request)"
  shows "sync_reference_product None gate verify core state = (state, Sync_Product_Refusal)"
  using assms by (simp add: sync_reference_product_def Let_def)

lemma sync_reference_detached_source_records_before_cut_or_proof:
  assumes "sync_read_operands core = Some request" "sync_execute_allowed state core request"
    "sync_endpoint_up gate" "\<not> sync_ordered_debit gate (sync_call request)"
    "sync_outcome_table state (sync_call request) = None" "\<not> sync_other_claimed gate (sync_call request)"
    "sync_registered_asset gate (fst (sync_key request))" "\<not> sync_source_connected gate"
  shows "sync_reference_product None gate verify core state =
    (sync_write_outcome state core request (Sync_Uncommitted Sync_Unavailable),
     Sync_Reference_Outcome (Sync_Uncommitted Sync_Unavailable))"
  using assms by (simp add: sync_reference_product_def Let_def)

lemma sync_reference_full_revision_cannot_publish_another_effect:
  assumes "sync_read_operands core = Some request" "\<not> sync_ordered_debit gate (sync_call request)"
    "sync_outcome_table state (sync_call request) = None" "sync_source_connected gate"
    "sync_fresh_assess verify state core request = Sync_Accept statement"
    "2^64 - 1 \<le> cut_revision (sync_current_cut state)"
  shows "sync_reference_product None gate verify core state = (state, Sync_Product_Refusal)"
  using assms by (simp add: sync_reference_product_def Let_def)

lemma sync_reference_commit_uses_pre_effect_position_and_next_cut:
  fixes state :: "('key, 'product) sync_receiver"
  assumes "sync_reference_product None gate verify core state =
    (next, Sync_Reference_Outcome (Sync_Committed position))"
    "sync_read_operands core = Some request" "sync_outcome_table state (sync_call request) = None"
  shows "position = cut_revision (sync_current_cut state)"
    "cut_revision (sync_current_cut next) = Suc position"
proof -
  obtain statement where committed_state: "next = sync_commit_record state core request statement"
    and position: "position = cut_revision (sync_current_cut state)"
    using assms by (auto simp: sync_reference_product_def Let_def split: if_splits sync_fresh_decision.splits)
  show "position = cut_revision (sync_current_cut state)" by (rule position)
  show "cut_revision (sync_current_cut next) = Suc position"
    using sync_commit_projects_the_single_stream_and_next_revision(4)
      [where state=state and core=core and request=request and a=statement]
    by (simp only: committed_state position)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_reference_transport_refusal_precedes_product
      sync_reference_reserved_debit_id_refuses_before_execution
      sync_reference_exact_retry_requires_current_execution_and_receipt
      sync_reference_other_call_collision_is_refused_without_record
      sync_reference_detached_source_records_before_cut_or_proof
      sync_reference_full_revision_cannot_publish_another_effect
      sync_reference_commit_uses_pre_effect_position_and_next_cut})
  then () else error "Unexpected oracle at the synchronization reference boundary"
\<close>

end
