theory Wire_Code_Operands_Regulated
  imports Wire_Code_Operands_Metadata
begin

definition code_optional_origin where
  "code_optional_origin words =
    (case words of [] \<Rightarrow> None | present # tail \<Rightarrow>
      if present = 0 then Some (None,tail)
      else if present = 1 then
        (case tail of domain # event # rest \<Rightarrow> Some (Some (domain,event),rest) | _ \<Rightarrow> None)
      else None)"

definition code_optional_word where
  "code_optional_word words =
    (case words of [] \<Rightarrow> None | present # tail \<Rightarrow>
      if present = 0 then Some (None,tail)
      else if present = 1 then
        (case tail of value # rest \<Rightarrow> Some (Some value,rest) | _ \<Rightarrow> None)
      else None)"

lemma a_nonboolean_optional_presence_is_a_format_failure:
  assumes "present \<notin> {0,1}"
  shows "code_optional_origin (present # tail) = None"
    "code_optional_word (present # tail) = None"
  using assms by (auto simp: code_optional_origin_def code_optional_word_def)

datatype code_legal_stage = Code_Source_Emission | Code_Receiving_Commit

record code_legal_fields =
  legal_action_number :: nat
  legal_officer :: nat
  legal_jurisdiction :: nat
  legal_basis :: nat
  legal_issuance_epoch :: nat
  legal_scope :: "nat set"
  legal_predecessor :: "(nat \<times> nat) option"
  legal_destination :: "nat option"
  legal_appeal_deadline :: "nat option"

definition code_parse_legal_fields where
  "code_parse_legal_fields deadline words =
    (case words of action # officer # jurisdiction # basis # epoch # tail \<Rightarrow>
      if action \<notin> {1..7} then None
      else Option.bind (code_take_ordered_set tail) (\<lambda>(scope,first).
        Option.bind (code_optional_origin first) (\<lambda>(predecessor,second).
          Option.bind (code_optional_word second) (\<lambda>(destination,last).
            if last \<noteq> [] then None else Some
              \<lparr>legal_action_number = action,legal_officer = officer,legal_jurisdiction = jurisdiction,
               legal_basis = basis,legal_issuance_epoch = epoch,legal_scope = scope,
               legal_predecessor = predecessor,legal_destination = destination,
               legal_appeal_deadline = code_product_deadline deadline\<rparr>)))
     | _ \<Rightarrow> None)"

datatype code_legal_result =
    Code_Legal_Refused wire_refusal
  | Code_Legal_Ready wire_native_call code_legal_stage code_legal_fields wire_bytes

definition code_decode_legal where
  "code_decode_legal core =
    (case code_native_call_prefix core of None \<Rightarrow> Code_Legal_Refused Invalid_Wire_Format | Some native \<Rightarrow>
      (case native_proof_bytes native of [proof] \<Rightarrow>
        if proof = [] then Code_Legal_Refused Invalid_Wire_Format
        else let operation = wire_opcode (wire_operation_body core) in
          if operation \<notin> {1,2} then Code_Legal_Refused Invalid_Wire_Format
          else (case code_parse_legal_fields (wire_deadline (wire_operation_body core)) (native_tail_words native) of
            None \<Rightarrow> Code_Legal_Refused Invalid_Wire_Format | Some parsed_fields \<Rightarrow>
              let stage = (if operation = 1 then Code_Source_Emission else Code_Receiving_Commit);
                  target = (if operation = 1 then fst (native_origin native) else native_destination native)
              in if wire_target_domain core \<noteq> target \<or> legal_issuance_epoch parsed_fields \<noteq> native_origin_epoch native
                 then Code_Legal_Refused Invalid_Wire_Source
                 else Code_Legal_Ready native stage parsed_fields proof)
       | _ \<Rightarrow> Code_Legal_Refused Invalid_Wire_Format))"

theorem a_source_legal_result_keeps_the_stage_endpoint_origin_epoch_and_proof:
  assumes "code_decode_legal core = Code_Legal_Ready native stage parsed_fields proof"
  shows "decode_native_call_prefix core = Some native"
    "native_proof_bytes native = [proof]" "proof \<noteq> []"
    "legal_issuance_epoch parsed_fields = native_origin_epoch native"
    "wire_target_domain core = (case stage of Code_Source_Emission \<Rightarrow> fst (native_origin native)
      | Code_Receiving_Commit \<Rightarrow> native_destination native)"
  using assms a_source_native_prefix_has_the_exact_product_header(1)
  by (auto simp: code_decode_legal_def Let_def split: option.splits list.splits if_splits)

record code_enforcement_fields =
  enforcement_officer :: nat
  enforcement_jurisdiction :: nat
  enforcement_basis :: nat
  enforcement_assets :: "nat set"
  enforcement_prior_seizure :: "(nat \<times> nat) option"
  enforcement_appeal_deadline :: "nat option"

definition code_parse_enforcement_fields where
  "code_parse_enforcement_fields deadline words =
    (case words of officer # jurisdiction # basis # tail \<Rightarrow>
      Option.bind (code_take_ordered_set tail) (\<lambda>(assets,first).
        Option.bind (code_optional_origin first) (\<lambda>(prior,last).
          if last \<noteq> [] then None else Some
            \<lparr>enforcement_officer = officer,enforcement_jurisdiction = jurisdiction,
             enforcement_basis = basis,enforcement_assets = assets,enforcement_prior_seizure = prior,
             enforcement_appeal_deadline = code_product_deadline deadline\<rparr>))
     | _ \<Rightarrow> None)"

record code_spend_fields =
  spend_reference :: nat
  spend_sender :: nat
  spend_recipient :: nat
  spend_kind_number :: nat
  spend_amount :: nat
  spend_enforcement :: "code_enforcement_fields option"
  spend_proof :: "wire_bytes option"

definition code_parse_spend_fields where
  "code_parse_spend_fields family deadline native =
    (case native_tail_words native of reference # sender # recipient # kind # tail \<Rightarrow>
      if \<not> ((family = Wire_State_Sync \<and> kind = 0) \<or> (family = Wire_Regulatory \<and> kind \<in> {1..4})) then None
      else (case native_proof_bytes native of [] \<Rightarrow> None | amount # proofs \<Rightarrow>
        Option.bind (code_product_amount amount) (\<lambda>value.
          let base = \<lparr>spend_reference = reference,spend_sender = sender,spend_recipient = recipient,
              spend_kind_number = kind,spend_amount = value,spend_enforcement = None,spend_proof = None\<rparr>
          in if family = Wire_Regulatory then
            (case proofs of [proof] \<Rightarrow> if proof = [] then None else
              map_option (\<lambda>parsed_fields. base\<lparr>spend_enforcement := Some parsed_fields,spend_proof := Some proof\<rparr>)
                (code_parse_enforcement_fields deadline tail)
             | _ \<Rightarrow> None)
          else if proofs \<noteq> [] \<or> deadline \<noteq> Deadline_Absent \<or> tail \<noteq> [] then None else Some base))
     | _ \<Rightarrow> None)"

datatype code_spend_result =
    Code_Spend_Refused wire_refusal
  | Code_Spend_Ready wire_native_call code_spend_fields

definition code_decode_spend where
  "code_decode_spend core =
    (case code_native_call_prefix core of None \<Rightarrow> Code_Spend_Refused Invalid_Wire_Format | Some native \<Rightarrow>
      (case code_parse_spend_fields (wire_message_family core) (wire_deadline (wire_operation_body core)) native of
         None \<Rightarrow> Code_Spend_Refused Invalid_Wire_Format | Some parsed_fields \<Rightarrow>
           if wire_target_domain core \<noteq> native_destination native then Code_Spend_Refused Invalid_Wire_Source
           else Code_Spend_Ready native parsed_fields))"

theorem a_source_spend_has_the_exact_destination_and_two_u64_amounts:
  assumes "code_decode_spend core = Code_Spend_Ready native parsed_fields"
  shows "decode_native_call_prefix core = Some native"
    "wire_target_domain core = native_destination native"
    "native_amount native < 2^64" "spend_amount parsed_fields < 2^64"
proof -
  have parts: "code_native_call_prefix core = Some native \<and>
      code_parse_spend_fields (wire_message_family core) (wire_deadline (wire_operation_body core)) native = Some parsed_fields \<and>
      wire_target_domain core = native_destination native"
    using assms by (auto simp: code_decode_spend_def split: option.splits if_splits)
  have prefix: "code_native_call_prefix core = Some native" using parts by simp
  show "decode_native_call_prefix core = Some native"
    by (rule a_source_native_prefix_has_the_exact_product_header(1)[OF prefix])
  show "wire_target_domain core = native_destination native" using parts by simp
  show "native_amount native < 2^64"
    by (rule a_source_native_prefix_has_the_exact_product_header(2)[OF prefix])
  have parsed: "code_parse_spend_fields (wire_message_family core)
      (wire_deadline (wire_operation_body core)) native = Some parsed_fields" using parts by simp
  obtain reference sender recipient kind tail where words:
      "native_tail_words native = reference # sender # recipient # kind # tail"
    using parsed by (auto simp: code_parse_spend_fields_def split: list.splits if_splits)
  obtain raw proofs where blobs: "native_proof_bytes native = raw # proofs"
    using parsed words by (auto simp: code_parse_spend_fields_def split: list.splits if_splits)
  have amount_present: "code_product_amount raw \<noteq> None"
  proof
    assume absent: "code_product_amount raw = None"
    have "code_parse_spend_fields (wire_message_family core)
        (wire_deadline (wire_operation_body core)) native = None"
      by (simp add: code_parse_spend_fields_def words blobs absent Let_def)
    then show False using parsed by simp
  qed
  obtain amount_value where amount: "code_product_amount raw = Some amount_value"
    using amount_present by (cases "code_product_amount raw") auto
  have exact: "spend_amount parsed_fields = amount_value"
  proof (cases "wire_message_family core = Wire_Regulatory")
    case False
    then show ?thesis using parsed words blobs amount
      by (auto simp: code_parse_spend_fields_def Let_def split: if_splits)
  next
    case True
    show ?thesis
    proof (cases proofs)
      case Nil
      have no_parse: "code_parse_spend_fields (wire_message_family core)
          (wire_deadline (wire_operation_body core)) native = None"
        by (simp add: code_parse_spend_fields_def words blobs amount True Nil Let_def)
      show ?thesis using parsed no_parse by simp
    next
      case (Cons auth_blob rest)
      have proof_blobs: "proofs = auth_blob # rest" by (rule Cons)
      show ?thesis
      proof (cases rest)
        case Nil
        then show ?thesis using parsed words blobs amount True proof_blobs
          by (cases "code_parse_enforcement_fields (wire_deadline (wire_operation_body core)) tail")
            (auto simp: code_parse_spend_fields_def Let_def split: if_splits)
      next
        case (Cons extra remaining)
        have no_parse: "code_parse_spend_fields (wire_message_family core)
            (wire_deadline (wire_operation_body core)) native = None"
          by (simp add: code_parse_spend_fields_def words blobs amount True proof_blobs Cons Let_def)
        show ?thesis using parsed no_parse by simp
      qed
    qed
  qed
  have bound: "amount_value < 2^64"
    using a_source_amount_has_no_high_byte_truncation[OF amount] by simp
  show "spend_amount parsed_fields < 2^64" using exact bound by simp
qed

end
