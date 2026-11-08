theory Wire_Code_Oracle_Transport
  imports Wire_Code_Operand_Tree
begin

datatype code_operand_verdict =
    Code_Operand_Accept
  | Code_Operand_Refuse wire_refusal
  | Code_Operand_Pending

definition code_ordinary_operand_verdict where
  "code_ordinary_operand_verdict core =
    (case code_decode_ordinary core of Code_Ordinary_Refused reason \<Rightarrow> Code_Operand_Refuse reason
     | Code_Ordinary_Ready native credential versions command \<Rightarrow> Code_Operand_Accept)"

definition code_transport_operand_verdict :: "wire_core \<Rightarrow> nat \<Rightarrow> code_operand_verdict" where
  "code_transport_operand_verdict core max_nesting =
    (case code_decode_operand_tree max_nesting core of
       Code_Tree_Refused reason \<Rightarrow> Code_Operand_Refuse reason
     | Code_Tree_Ready decoded \<Rightarrow> Code_Operand_Accept
     | Code_Tree_Pending \<Rightarrow> Code_Operand_Pending)"

fun code_transport_refusal_number :: "wire_refusal \<Rightarrow> nat" where
  "code_transport_refusal_number Invalid_Wire_Format = 70"
| "code_transport_refusal_number Unsupported_Wire_Version = 71"
| "code_transport_refusal_number Invalid_Wire_Source = 72"
| "code_transport_refusal_number Invalid_Wire_Signature = 73"
| "code_transport_refusal_number Invalid_Wire_Threshold = 74"
| "code_transport_refusal_number Wire_TTL_Expired = 54"
| "code_transport_refusal_number Wire_TTL_Invalid = 75"
| "code_transport_refusal_number Conflicting_Wire_Replay = 76"

datatype code_transport_verdict =
    Code_Transport_First
  | Code_Transport_Identical
  | Code_Transport_Refusal nat
  | Code_Transport_Pending

definition code_transport_refusal where
  "code_transport_refusal prior reason = (Code_Transport_Refusal (code_transport_refusal_number reason),prior)"

definition code_transport_after_operands where
  "code_transport_after_operands operand_check packet max_nesting prior =
    (case operand_check (packet_core packet) max_nesting of
       Code_Operand_Pending \<Rightarrow> (Code_Transport_Pending,prior)
     | Code_Operand_Refuse reason \<Rightarrow> code_transport_refusal prior reason
     | Code_Operand_Accept \<Rightarrow>
       (let exact = encode_wire_core (packet_core packet) in
        case code_compare_binding prior exact of
          Code_First \<Rightarrow> (Code_Transport_First,Some exact)
        | Code_Identical \<Rightarrow> (Code_Transport_Identical,prior)
        | Code_Replay_Conflict \<Rightarrow> code_transport_refusal prior Conflicting_Wire_Replay))"

definition code_transport_oracle ::
  "(wire_core \<Rightarrow> nat \<Rightarrow> code_operand_verdict) \<Rightarrow> wire_bytes \<Rightarrow> wire_boundary \<Rightarrow>
    nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> wire_bytes option \<Rightarrow>
    (code_transport_verdict \<times> wire_bytes option)" where
  "code_transport_oracle operand_check bytes authority max_nesting signature_valid attestation_valid prior =
    (if negotiated_version (boundary_profile authority) \<noteq> 6
     then code_transport_refusal prior Unsupported_Wire_Version
     else case code_check_declared_version bytes (boundary_max_frame authority) of
       Some reason \<Rightarrow> code_transport_refusal prior reason
     | None \<Rightarrow> (case decode_wire_packet bytes of None \<Rightarrow> code_transport_refusal prior Invalid_Wire_Format
       | Some packet \<Rightarrow>
         (case code_admit_packet (\<lambda>_ _ _. signature_valid) packet authority of
            Some reason \<Rightarrow> code_transport_refusal prior reason
          | None \<Rightarrow> if \<not> attestation_valid then code_transport_refusal prior Invalid_Wire_Source
            else code_transport_after_operands operand_check packet max_nesting prior)))"

definition code_partial_transport_oracle where
  "code_partial_transport_oracle = code_transport_oracle code_transport_operand_verdict"

text \<open>
  Code_Transport_Pending is deliberately not an accept or a refusal.  A
  strict differential runner must fail if it encounters that constructor.
  All protocol operand families now have direct executable definitions,
  including recursive receipts/responses and fixed-schema governance JSON.
  Native validation and the full differential execution remain separate.
  Crypto verification and host attestation are the two injected booleans.
\<close>

lemma every_refused_transport_keeps_the_prior_binding:
  assumes "code_transport_oracle operand_check bytes authority max_nesting signature_valid attestation_valid prior =
    (Code_Transport_Refusal number,after)"
  shows "after = prior"
  using assms
  by (auto simp: code_transport_oracle_def code_transport_after_operands_def code_transport_refusal_def
    Let_def split: option.splits code_operand_verdict.splits code_arrival.splits if_splits)

lemma an_unfinished_operand_scope_cannot_be_reported_as_an_acceptance:
  assumes "operand_check (packet_core packet) max_nesting = Code_Operand_Pending"
  shows "code_transport_after_operands operand_check packet max_nesting prior = (Code_Transport_Pending,prior)"
  using assms by (simp add: code_transport_after_operands_def)

lemma a_conflicting_retained_core_is_never_overwritten:
  assumes "operand_check (packet_core packet) max_nesting = Code_Operand_Accept"
    "prior \<noteq> encode_wire_core (packet_core packet)"
  shows "code_transport_after_operands operand_check packet max_nesting (Some prior) =
    (Code_Transport_Refusal 76,Some prior)"
  using assms
  by (simp add: code_transport_after_operands_def code_compare_binding_def code_transport_refusal_def Let_def)

end
