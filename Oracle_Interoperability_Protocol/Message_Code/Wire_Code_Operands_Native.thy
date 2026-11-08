theory Wire_Code_Operands_Native
  imports Wire_Code_Admission Wire_Code_Amounts "OIP_Product.Wire_Debit_Bridge"
begin

definition code_native_call_prefix :: "wire_core \<Rightarrow> wire_native_call option" where
  "code_native_call_prefix core =
    (let body = wire_operation_body core; words = wire_words body in
      if length words < 11 then None
      else case wire_blobs body of [] \<Rightarrow> None | amount # proofs \<Rightarrow>
        map_option (\<lambda>value.
          \<lparr>native_reference = words ! 0,native_id = (wire_principal core,words ! 1),
           native_session = words ! 2,
           native_cut = \<lparr>cut_authority_epoch = wire_authority_epoch core,cut_revision = words ! 3\<rparr>,
           native_origin_epoch = words ! 4,native_origin = (words ! 5,words ! 6),
           native_asset = words ! 7,native_funding_owner = words ! 8,native_destination = words ! 9,
           native_recipient = words ! 10,native_amount = value,
           native_tail_words = drop 11 words,native_proof_bytes = proofs\<rparr>)
          (code_product_amount amount))"

theorem source_native_prefix_is_the_existing_prefix_with_its_actual_amount_limit:
  "code_native_call_prefix core =
    (case decode_native_call_prefix core of None \<Rightarrow> None | Some native \<Rightarrow>
      if native_amount native < 2^64 then Some native else None)"
  by (auto simp: code_native_call_prefix_def decode_native_call_prefix_def
    the_source_amount_check_is_exactly_the_model_value_and_u64_limit Let_def
    split: list.splits option.splits if_splits)

lemma a_source_native_prefix_has_the_exact_product_header:
  assumes "code_native_call_prefix core = Some native"
  shows "decode_native_call_prefix core = Some native" "native_amount native < 2^64"
    "fst (native_id native) = wire_principal core"
    "cut_authority_epoch (native_cut native) = wire_authority_epoch core"
    "native_tail_words native = drop 11 (wire_words (wire_operation_body core))"
  using assms
  by (auto simp: source_native_prefix_is_the_existing_prefix_with_its_actual_amount_limit
    decode_native_call_prefix_def Let_def split: option.splits list.splits if_splits)

lemma parsed_version_pairs_consume_exactly_twice_the_declared_count:
  assumes "read_wire_versions count words = Some (versions,rest)"
  shows "length versions = count" "length words = 2 * count + length rest"
  using assms
  by (induction count arbitrary: words versions rest)
    (auto split: list.splits option.splits prod.splits)

definition code_read_wire_versions where
  "code_read_wire_versions count words =
    (if 2 * count < 2^64 then read_wire_versions count words else None)"

theorem the_source_checked_pair_count_does_not_reject_any_representable_list:
  assumes limit: "length words < 2^64"
  shows "code_read_wire_versions count words = read_wire_versions count words"
proof (cases "2 * count < 2^64")
  case True
  then show ?thesis by (simp add: code_read_wire_versions_def)
next
  case False
  have no_parse: "read_wire_versions count words = None"
  proof (cases "read_wire_versions count words")
    case None
    then show ?thesis .
  next
    case (Some pair)
    obtain versions rest where pair: "pair = (versions,rest)" by (cases pair) auto
    have length: "length words = 2 * count + length rest"
      by (rule parsed_version_pairs_consume_exactly_twice_the_declared_count(2))
        (use Some pair in simp)
    show ?thesis using False limit length by arith
  qed
  show ?thesis using False no_parse by (simp add: code_read_wire_versions_def)
qed

fun code_ordinary_endpoint where
  "code_ordinary_endpoint native (Wire_Deliver reference) = native_destination native"
| "code_ordinary_endpoint native command = fst (native_origin native)"

fun code_ordinary_proof_count :: "ordinary_wire_command \<Rightarrow> nat" where
  "code_ordinary_proof_count (Wire_Record_Terminal kind reference) = 1"
| "code_ordinary_proof_count (Wire_Refund generation reference) = 1"
| "code_ordinary_proof_count (Wire_Cancel generation) = 1"
| "code_ordinary_proof_count (Wire_Fence generation) = 1"
| "code_ordinary_proof_count (Wire_Reconcile generation reference) = 1"
| "code_ordinary_proof_count (Wire_Preempt duration) = 1"
| "code_ordinary_proof_count command = 0"

definition code_ordinary_proofs_allowed where
  "code_ordinary_proofs_allowed native command \<longleftrightarrow>
    length (native_proof_bytes native) = code_ordinary_proof_count command \<and>
    (\<forall>proof \<in> set (native_proof_bytes native). proof \<noteq> [])"

datatype code_ordinary_result =
    Code_Ordinary_Refused wire_refusal
  | Code_Ordinary_Ready wire_native_call "product_lock_credential option" "(nat \<times> nat) list" ordinary_wire_command

text \<open>
  read_wire_versions and decode_ordinary_tail are the existing structural
  parsers.  The checked-multiply source guard is redundant on a list whose
  length fits the 64-bit host, by the preceding count theorem.  The extra
  source checks below retain their actual order and distinct source error.
\<close>

definition code_decode_ordinary :: "wire_core \<Rightarrow> code_ordinary_result" where
  "code_decode_ordinary core =
    (if wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent
     then Code_Ordinary_Refused Invalid_Wire_Format
     else case code_native_call_prefix core of None \<Rightarrow> Code_Ordinary_Refused Invalid_Wire_Format | Some native \<Rightarrow>
       (case decode_ordinary_operands core native of None \<Rightarrow> Code_Ordinary_Refused Invalid_Wire_Format
        | Some (credential,versions,command) \<Rightarrow>
          if wire_target_domain core \<noteq> code_ordinary_endpoint native command
          then Code_Ordinary_Refused Invalid_Wire_Source
          else if \<not> code_ordinary_proofs_allowed native command
          then Code_Ordinary_Refused Invalid_Wire_Format
          else Code_Ordinary_Ready native credential versions command))"

theorem every_source_ordinary_result_retains_the_existing_decoded_operands:
  assumes "code_decode_ordinary core = Code_Ordinary_Ready native credential versions command"
  shows "decode_native_call_prefix core = Some native"
    "native_amount native < 2^64"
    "decode_ordinary_operands core native = Some (credential,versions,command)"
    "wire_deadline (wire_operation_body core) = Deadline_Absent"
    "wire_target_domain core = code_ordinary_endpoint native command"
    "code_ordinary_proofs_allowed native command"
proof -
  have selected: "code_native_call_prefix core = Some native"
    and fields: "decode_ordinary_operands core native = Some (credential,versions,command)"
    and extra: "wire_deadline (wire_operation_body core) = Deadline_Absent"
      "wire_target_domain core = code_ordinary_endpoint native command"
      "code_ordinary_proofs_allowed native command"
    using assms
    by (auto simp: code_decode_ordinary_def split: option.splits prod.splits if_splits)
  show "decode_native_call_prefix core = Some native" "native_amount native < 2^64"
    using a_source_native_prefix_has_the_exact_product_header[OF selected] by auto
  show "decode_ordinary_operands core native = Some (credential,versions,command)" by (rule fields)
  show "wire_deadline (wire_operation_body core) = Deadline_Absent"
    "wire_target_domain core = code_ordinary_endpoint native command"
    "code_ordinary_proofs_allowed native command" by (rule extra)+
qed

theorem every_source_debit_meets_the_existing_debit_selector_header:
  assumes accepted: "code_decode_ordinary core = Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
  shows "native_debit_header_allowed core native"
proof -
  note fields = every_source_ordinary_result_retains_the_existing_decoded_operands[OF accepted]
  have no_proof: "native_proof_bytes native = []"
    using fields(6) by (simp add: code_ordinary_proofs_allowed_def)
  show ?thesis using fields(2,4,5) no_proof
    by (simp add: native_debit_header_allowed_def)
qed

theorem an_exact_source_debit_attachment_reaches_the_existing_product_action:
  assumes accepted: "code_decode_ordinary core = Code_Ordinary_Ready native credential versions (Wire_Debit generation)"
    and attached: "attach native = Some request"
    and exact: "signed_debit_request_matches native request"
  shows "select_wire_debit route token endorsement attach core =
    Some (native_funding_owner native,
      debit_action_from_exact_operands route token endorsement core native credential versions generation request)"
  using every_source_ordinary_result_retains_the_existing_decoded_operands[OF accepted]
    every_source_debit_meets_the_existing_debit_selector_header[OF accepted] attached exact
  by (simp add: select_wire_debit_def)

lemma source_ordinary_deadlines_are_refused_before_the_native_call:
  "wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent \<Longrightarrow>
    code_decode_ordinary core = Code_Ordinary_Refused Invalid_Wire_Format"
  by (simp add: code_decode_ordinary_def)

lemma the_source_endpoint_refusal_precedes_the_proof_count_refusal:
  assumes "wire_deadline (wire_operation_body core) = Deadline_Absent"
    "code_native_call_prefix core = Some native"
    "decode_ordinary_operands core native = Some (credential,versions,command)"
    "wire_target_domain core \<noteq> code_ordinary_endpoint native command"
  shows "code_decode_ordinary core = Code_Ordinary_Refused Invalid_Wire_Source"
  using assms by (simp add: code_decode_ordinary_def)

fun code_product_deadline where
  "code_product_deadline Deadline_Absent = None"
| "code_product_deadline Deadline_Indefinite = None"
| "code_product_deadline (Deadline_At seconds) = Some seconds"

lemma the_two_no_appeal_deadline_encodings_have_the_same_product_value:
  "code_product_deadline Deadline_Absent = code_product_deadline Deadline_Indefinite"
  by simp

end
