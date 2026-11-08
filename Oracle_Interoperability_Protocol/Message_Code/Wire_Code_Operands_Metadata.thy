theory Wire_Code_Operands_Metadata
  imports Wire_Code_Operands_Native
begin

definition code_decode_query_nonreceipt where
  "code_decode_query_nonreceipt core =
    (if wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent
     then None else decode_wire_query_body core)"

theorem a_source_nonreceipt_query_has_the_existing_product_query_and_no_deadline:
  assumes "code_decode_query_nonreceipt core = Some query"
  shows "decode_wire_query_body core = Some query"
    "wire_deadline (wire_operation_body core) = Deadline_Absent"
  using assms by (auto simp: code_decode_query_nonreceipt_def split: if_splits)

lemma a_present_query_deadline_is_a_source_format_refusal:
  "wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent \<Longrightarrow>
    code_decode_query_nonreceipt core = None"
  by (simp add: code_decode_query_nonreceipt_def)

definition code_take_ordered_set :: "nat list \<Rightarrow> (nat set \<times> nat list) option" where
  "code_take_ordered_set words =
    (case words of [] \<Rightarrow> None | count # tail \<Rightarrow>
      if count > length tail then None
      else let items = take count tail in
        if sorted_wrt (<) items then Some (set items,drop count tail) else None)"

lemma a_source_counted_set_retains_exactly_its_counted_ordered_items:
  assumes "code_take_ordered_set words = Some (values,rest)"
  obtains count items where "words = count # items @ rest" "length items = count"
    "sorted_wrt (<) items" "values = set items"
proof -
  obtain count tail where words: "words = count # tail"
    and count: "count \<le> length tail" and sorted: "sorted_wrt (<) (take count tail)"
    and members: "values = set (take count tail)" and rest: "rest = drop count tail"
    using assms by (auto simp: code_take_ordered_set_def Let_def split: list.splits if_splits)
  have exact: "words = count # take count tail @ rest" using words rest by simp
  have length: "length (take count tail) = count" using count by simp
  show thesis by (rule that[OF exact length sorted members])
qed

datatype code_heartbeat_fields =
    Code_Capabilities nat nat "nat set" "nat set" "nat set" "nat set"
  | Code_Liveness nat nat

definition code_decode_heartbeat where
  "code_decode_heartbeat core =
    (let body = wire_operation_body core in
     if wire_blobs body \<noteq> [] \<or> wire_deadline body \<noteq> Deadline_Absent then None
     else case wire_words body of challenge # expires # tail \<Rightarrow>
       if wire_opcode body = 1 then
         Option.bind (code_take_ordered_set tail) (\<lambda>(versions,first).
          Option.bind (code_take_ordered_set first) (\<lambda>(families,second).
           Option.bind (code_take_ordered_set second) (\<lambda>(atomicities,third).
            Option.bind (code_take_ordered_set third) (\<lambda>(schemes,last).
             if last = [] then Some (Code_Capabilities challenge expires versions families atomicities schemes) else None))))
       else if tail = [] then Some (Code_Liveness challenge expires) else None
     | _ \<Rightarrow> None)"

record code_raw_capability_offer =
  capability_deployment :: nat
  capability_sender :: nat
  capability_receiver :: nat
  capability_challenge :: nat
  capability_expires :: nat
  capability_versions :: "nat set"
  capability_families :: "nat set"
  capability_atomicities :: "nat set"
  capability_schemes :: "nat set"

definition code_capability_offer where
  "code_capability_offer core parsed_fields =
    (case parsed_fields of Code_Capabilities challenge expires versions families atomicities schemes \<Rightarrow>
      Some \<lparr>capability_deployment = wire_deployment core,capability_sender = wire_source_domain core,
       capability_receiver = wire_target_domain core,capability_challenge = challenge,capability_expires = expires,
       capability_versions = versions,capability_families = families,capability_atomicities = atomicities,
       capability_schemes = schemes\<rparr>
     | Code_Liveness challenge expires \<Rightarrow> None)"

lemma capabilities_keep_the_exact_outer_deployment_and_peer_directions:
  assumes "code_capability_offer core parsed_fields = Some offer"
  shows "capability_deployment offer = wire_deployment core"
    "capability_sender offer = wire_source_domain core"
    "capability_receiver offer = wire_target_domain core"
proof -
  show "capability_deployment offer = wire_deployment core"
    using assms by (cases parsed_fields) (auto simp: code_capability_offer_def)
  show "capability_sender offer = wire_source_domain core"
    using assms by (cases parsed_fields) (auto simp: code_capability_offer_def)
  show "capability_receiver offer = wire_target_domain core"
    using assms by (cases parsed_fields) (auto simp: code_capability_offer_def)
qed

lemma a_liveness_record_has_exactly_two_words:
  assumes "wire_opcode (wire_operation_body core) \<noteq> 1"
    "code_decode_heartbeat core = Some (Code_Liveness challenge expires)"
  shows "wire_words (wire_operation_body core) = [challenge,expires]"
  using assms by (auto simp: code_decode_heartbeat_def Let_def split: list.splits if_splits)

lemma heartbeat_payloads_cannot_enter_the_reference_product:
  assumes "wire_message_family core = Wire_Heartbeat"
  shows "code_check_operation code_reference_accepts core = Some Unsupported_Wire_Version"
  using assms by (simp add: code_check_operation_def)

end
