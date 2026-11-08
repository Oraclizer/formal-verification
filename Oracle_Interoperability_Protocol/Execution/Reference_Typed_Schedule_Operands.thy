theory Reference_Typed_Schedule_Operands
  imports Reference_Queue_Code Reference_Read_Code
begin

record ('primary, 'observation) rust_scheduled_payload =
  rust_scheduled_queue :: "'primary rust_queue_image"
  rust_scheduled_epoch :: nat
  rust_scheduled_revision :: nat
  rust_scheduled_prefixes :: "'observation list"

datatype 'value typed_schedule_result = Typed_ACK bool | Typed_Current "(product_cut \<times> 'value) option"

definition rust_typed_schedule_matches where
  "rust_typed_schedule_matches primary_related code model \<longleftrightarrow>
     rust_queue_matches primary_related (rust_scheduled_queue code) (fst model) \<and>
     native_read_history_related (rust_scheduled_epoch code) (rust_scheduled_revision code)
        (rust_scheduled_prefixes code) (snd model)"

definition rust_scheduled_ack where
  "rust_scheduled_ack verify ack code =
    (let result = rust_acknowledge_row verify ack (rust_scheduled_queue code)
     in (code\<lparr>rust_scheduled_queue := fst result\<rparr>, Typed_ACK (snd result)))"

definition rust_scheduled_current where
  "rust_scheduled_current permitted read expected code =
    (code, Typed_Current (native_current_read_value permitted read expected (rust_scheduled_epoch code)
      (rust_scheduled_revision code) (rust_scheduled_prefixes code)))"

lemma the_signed_ack_operand_simulates_its_product_queue_step_and_typed_reply:
  assumes related: "rust_typed_schedule_matches primary_related code model"
    and targets: "native_queue_has_one_target (fst model)"
  shows "let result = rust_scheduled_ack verify ack code;
       spec = execute_settlement_action verify (Exact_Acknowledge ack) (fst model)
    in rust_typed_schedule_matches primary_related (fst result) (fst spec, snd model) \<and>
       (\<exists>value. snd result = Typed_ACK value \<and> snd spec = Settlement_Changed value)"
proof -
  have queue: "rust_queue_matches primary_related (rust_scheduled_queue code) (fst model)"
    using related by (simp add: rust_typed_schedule_matches_def)
  note ack = rust_ack_consumes_the_related_queue_and_preserves_its_primary_and_reply[OF queue targets,
      where verify=verify and ack=ack]
  show ?thesis using ack related
    by (auto simp: rust_typed_schedule_matches_def rust_scheduled_ack_def Let_def)
qed

lemma the_signed_current_operand_simulates_the_model_cut_value_without_a_queue_write:
  assumes related: "rust_typed_schedule_matches primary_related code model"
  shows "let result = rust_scheduled_current permitted read expected code
    in rust_typed_schedule_matches primary_related (fst result) model \<and>
       snd result = Typed_Current (current_reference_observation permitted read expected (snd model))"
proof -
  have history: "native_read_history_related (rust_scheduled_epoch code) (rust_scheduled_revision code)
    (rust_scheduled_prefixes code) (snd model)"
    using related by (simp add: rust_typed_schedule_matches_def)
  show ?thesis using related the_native_cut_and_its_selected_prefixes_give_the_same_model_values(1)
      [OF history, where permitted=permitted and read=read and expected=expected]
    by (simp add: rust_scheduled_current_def Let_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_signed_ack_operand_simulates_its_product_queue_step_and_typed_reply
      the_signed_current_operand_simulates_the_model_cut_value_without_a_queue_write})
  then () else error "Unexpected oracle in typed schedule operands"
\<close>

end
