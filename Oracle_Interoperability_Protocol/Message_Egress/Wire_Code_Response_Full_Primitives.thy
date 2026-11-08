theory Wire_Code_Response_Full_Primitives
  imports Wire_Code_Response_Full_Getters
begin

type_synonym code_full_hash_table = "(wire_bytes \<times> wire_bytes) list"
type_synonym code_full_sign_table = "(wire_bytes \<times> wire_bytes \<times> wire_bytes) list"
type_synonym code_full_verify_table = "(wire_bytes \<times> wire_bytes \<times> wire_bytes \<times> bool) list"

fun code_full_parse_hash_rows :: "nat list list \<Rightarrow> code_full_hash_table option" where
  "code_full_parse_hash_rows [] = Some []"
| "code_full_parse_hash_rows (oip_full_message # oip_full_digest # oip_full_rest) =
    (if length oip_full_digest \<noteq> 32 \<or> \<not> list_all wire_octets [oip_full_message,oip_full_digest]
     then None else map_option (Cons (oip_full_message,oip_full_digest))
       (code_full_parse_hash_rows oip_full_rest))"
| "code_full_parse_hash_rows [_] = None"

fun code_full_parse_sign_rows :: "nat list list \<Rightarrow> code_full_sign_table option" where
  "code_full_parse_sign_rows [] = Some []"
| "code_full_parse_sign_rows (oip_full_key # oip_full_message # oip_full_signature # oip_full_rest) =
    (if length oip_full_key \<noteq> 32 \<or> length oip_full_signature \<noteq> 64 \<or>
       \<not> list_all wire_octets [oip_full_key,oip_full_message,oip_full_signature]
     then None else map_option (Cons (oip_full_key,oip_full_message,oip_full_signature))
       (code_full_parse_sign_rows oip_full_rest))"
| "code_full_parse_sign_rows [_] = None"
| "code_full_parse_sign_rows [_,_] = None"

fun code_full_parse_verify_rows :: "nat list list \<Rightarrow> code_full_verify_table option" where
  "code_full_parse_verify_rows [] = Some []"
| "code_full_parse_verify_rows
      (oip_full_key # oip_full_message # oip_full_signature # oip_full_answer # oip_full_rest) =
    (if length oip_full_key \<noteq> 32 \<or>
       \<not> list_all wire_octets [oip_full_key,oip_full_message,oip_full_signature] \<or>
       (oip_full_answer \<noteq> [0] \<and> oip_full_answer \<noteq> [1])
     then None else map_option (Cons (oip_full_key,oip_full_message,oip_full_signature,oip_full_answer = [1]))
       (code_full_parse_verify_rows oip_full_rest))"
| "code_full_parse_verify_rows [_] = None"
| "code_full_parse_verify_rows [_,_] = None"
| "code_full_parse_verify_rows [_,_,_] = None"

definition code_full_tables_from_integer ::
  "integer list list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow>
    (code_full_hash_table \<times> code_full_sign_table \<times> code_full_verify_table) option" where
  "code_full_tables_from_integer = (\<lambda>oip_full_hash_rows oip_full_sign_rows oip_full_verify_rows.
    if \<not> code_integer_octet_values (concat (oip_full_hash_rows @ oip_full_sign_rows @ oip_full_verify_rows))
    then None
    else Option.bind (code_full_parse_hash_rows (map (map nat_of_integer) oip_full_hash_rows))
      (\<lambda>oip_full_hashes.
        Option.bind (code_full_parse_sign_rows (map (map nat_of_integer) oip_full_sign_rows))
          (\<lambda>oip_full_signatures.
            Option.bind (code_full_parse_verify_rows (map (map nat_of_integer) oip_full_verify_rows))
              (\<lambda>oip_full_verifications.
                if distinct (map fst oip_full_hashes) \<and>
                   distinct (map (\<lambda>(oip_full_key,oip_full_message,oip_full_signature).
                     (oip_full_key,oip_full_message)) oip_full_signatures) \<and>
                   distinct (map (\<lambda>(oip_full_key,oip_full_message,oip_full_signature,oip_full_answer).
                     (oip_full_key,oip_full_message,oip_full_signature)) oip_full_verifications)
                then Some (oip_full_hashes,oip_full_signatures,oip_full_verifications) else None))))"

definition code_full_lookup_hash :: "code_full_hash_table \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes option" where
  "code_full_lookup_hash = (\<lambda>oip_full_table oip_full_message.
    map_option snd (List.find (\<lambda>oip_full_item. fst oip_full_item = oip_full_message) oip_full_table))"

definition code_full_lookup_sign ::
  "code_full_sign_table \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes option" where
  "code_full_lookup_sign = (\<lambda>oip_full_table oip_full_key oip_full_message.
    map_option (\<lambda>(oip_full_record_key,oip_full_record_message,oip_full_signature). oip_full_signature)
      (List.find (\<lambda>(oip_full_record_key,oip_full_record_message,oip_full_signature).
        oip_full_record_key = oip_full_key \<and> oip_full_record_message = oip_full_message) oip_full_table))"

definition code_full_lookup_verify ::
  "code_full_verify_table \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool option" where
  "code_full_lookup_verify = (\<lambda>oip_full_table oip_full_key oip_full_message oip_full_signature.
    map_option (\<lambda>(oip_full_record_key,oip_full_record_message,oip_full_record_signature,oip_full_answer). oip_full_answer)
      (List.find (\<lambda>(oip_full_record_key,oip_full_record_message,oip_full_record_signature,oip_full_answer).
        oip_full_record_key = oip_full_key \<and> oip_full_record_message = oip_full_message \<and>
        oip_full_record_signature = oip_full_signature) oip_full_table))"

definition code_full_hash :: "code_full_hash_table \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes" where
  "code_full_hash = (\<lambda>oip_full_table oip_full_message.
    case code_full_lookup_hash oip_full_table oip_full_message of Some oip_full_digest \<Rightarrow> oip_full_digest
     | None \<Rightarrow> Code.abort (STR ''OIP_PRIMITIVE_MISSING_SHA256'') (\<lambda>_. []))"

definition code_full_sign ::
  "code_full_sign_table \<Rightarrow> wire_bytes \<Rightarrow> unit \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes" where
  "code_full_sign = (\<lambda>oip_full_table oip_full_key oip_full_ignored oip_full_message.
    case code_full_lookup_sign oip_full_table oip_full_key oip_full_message of
       Some oip_full_signature \<Rightarrow> oip_full_signature
     | None \<Rightarrow> Code.abort (STR ''OIP_PRIMITIVE_MISSING_ED25519_SIGN'') (\<lambda>_. []))"

definition code_full_verify ::
  "code_full_verify_table \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool" where
  "code_full_verify = (\<lambda>oip_full_table oip_full_key oip_full_message oip_full_signature.
    case code_full_lookup_verify oip_full_table oip_full_key oip_full_message oip_full_signature of
       Some oip_full_answer \<Rightarrow> oip_full_answer
     | None \<Rightarrow> Code.abort (STR ''OIP_PRIMITIVE_MISSING_ED25519_VERIFY'') (\<lambda>_. False))"

definition code_full_probe_verify ::
  "code_full_verify_table \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool" where
  "code_full_probe_verify = (\<lambda>oip_full_table oip_full_key oip_full_message oip_full_signature.
    (case code_full_lookup_verify oip_full_table oip_full_key oip_full_message oip_full_signature of None \<Rightarrow> False | Some oip_full_probe_answer \<Rightarrow> oip_full_probe_answer))"

definition code_full_query_blob :: "wire_bytes \<Rightarrow> nat list" where
  "code_full_query_blob = (\<lambda>oip_full_bytes. length oip_full_bytes # oip_full_bytes)"

definition code_full_hash_query :: "wire_bytes \<Rightarrow> nat list" where
  "code_full_hash_query = (\<lambda>oip_full_message. 0 # code_full_query_blob oip_full_message)"

definition code_full_sign_query :: "wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> nat list" where
  "code_full_sign_query = (\<lambda>oip_full_key oip_full_message.
    1 # code_full_query_blob oip_full_key @ code_full_query_blob oip_full_message)"

definition code_full_verify_query :: "wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> nat list" where
  "code_full_verify_query = (\<lambda>oip_full_key oip_full_message oip_full_signature.
    2 # code_full_query_blob oip_full_key @ code_full_query_blob oip_full_message @ code_full_query_blob oip_full_signature)"

definition code_full_need_verify ::
  "code_full_verify_table \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> nat list list" where
  "code_full_need_verify = (\<lambda>oip_full_table oip_full_key oip_full_message oip_full_signature.
    if code_full_lookup_verify oip_full_table oip_full_key oip_full_message oip_full_signature = None
    then [code_full_verify_query oip_full_key oip_full_message oip_full_signature] else [])"

lemma a_hash_transcript_is_selected_only_by_the_model_preimage:
  fixes oip_full_table :: code_full_hash_table and oip_full_message oip_full_digest :: wire_bytes
  assumes "code_full_lookup_hash oip_full_table oip_full_message = Some oip_full_digest"
  shows "code_full_hash oip_full_table oip_full_message = oip_full_digest"
  using assms by (simp add: code_full_hash_def)

lemma a_signature_transcript_is_selected_by_both_key_and_model_preimage:
  fixes oip_full_table :: code_full_sign_table
    and oip_full_key oip_full_message oip_full_signature :: wire_bytes
  assumes "code_full_lookup_sign oip_full_table oip_full_key oip_full_message = Some oip_full_signature"
  shows "code_full_sign oip_full_table oip_full_key () oip_full_message = oip_full_signature"
  using assms by (simp add: code_full_sign_def)

lemma a_verification_transcript_is_selected_by_key_preimage_and_signature:
  fixes oip_full_table :: code_full_verify_table
    and oip_full_key oip_full_message oip_full_signature :: wire_bytes
    and oip_full_answer :: bool
  assumes "code_full_lookup_verify oip_full_table oip_full_key oip_full_message oip_full_signature = Some oip_full_answer"
  shows "code_full_verify oip_full_table oip_full_key oip_full_message oip_full_signature = oip_full_answer"
  using assms by (simp add: code_full_verify_def)

lemma a_true_primitive_probe_cannot_come_from_a_missing_record:
  fixes oip_full_table :: code_full_verify_table
    and oip_full_key oip_full_message oip_full_signature :: wire_bytes
  assumes "code_full_probe_verify oip_full_table oip_full_key oip_full_message oip_full_signature"
  shows "code_full_lookup_verify oip_full_table oip_full_key oip_full_message oip_full_signature = Some True"
  using assms by (auto simp: code_full_probe_verify_def split: option.splits)

text \<open>
  Only the named SHA256 and Ed25519 primitives are supplied by transcripts.
  No row says that an entire sender/client consumer succeeded. Logical
  facts above require the exact lookup; Code.abort is the standard target
  code error on a missing executable callback, not a proof escape. A strict
  standalone consumer must fail any such error and preserve its raw output.
  The default-False probe is used only by the request planner to find an
  unresolved verification point. No sender/client protocol result is ever
  returned by that probe; actual consumers use the strict callback.
\<close>

end
