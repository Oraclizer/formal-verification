theory Sync_V061_Supplier_ABI
  imports "OIP_Sync_V061_Concrete_Supplier_V2.Sync_V061_Concrete_Supplier"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen" "HOL-Library.Code_Target_Nat"
begin

type_synonym supplier_abi_stores =
  "integer list \<times> integer list \<times> integer list \<times> integer list option"
type_synonym supplier_abi_token =
  "supplier_abi_stores \<times> (integer \<times> integer list) \<times> integer list \<times> integer"
type_synonym supplier_abi_vote = "supplier_abi_token \<times> integer \<times> integer list"
type_synonym supplier_abi_record = "integer list \<times> integer list"

declare [[code drop: sync_parse_votes]]

lemma supplier_abi_sync_parse_votes_code [code]:
  "sync_parse_votes count raw =
    (if count = 0 then []
     else (sync_take_word raw, take 64 (drop 8 raw)) # sync_parse_votes (count - 1) (drop 72 raw))"
  by (cases count) simp_all

definition supplier_abi_octets :: "integer list \<Rightarrow> bool" where
  "supplier_abi_octets bytes = list_all (\<lambda>octet. 0 \<le> octet \<and> octet < 256) bytes"

definition supplier_abi_fixed where
  "supplier_abi_fixed width bytes \<longleftrightarrow> length bytes = width \<and> supplier_abi_octets bytes"

definition supplier_abi_u64 :: "integer \<Rightarrow> bool" where
  "supplier_abi_u64 word \<longleftrightarrow> 0 \<le> word \<and> word < 2^64"

definition supplier_abi_decode_token ::
  "supplier_abi_token \<Rightarrow> (wire_bytes, wire_bytes) supplier_selection option" where
  "supplier_abi_decode_token input =
    (case input of ((journal_id,witness_id,terminal_cfg,sync_cfg),(revision,mark_bytes),statement_bytes,quorum) \<Rightarrow>
      if supplier_abi_fixed 32 journal_id \<and> supplier_abi_fixed 32 witness_id \<and>
         supplier_abi_fixed 32 terminal_cfg \<and>
         (case sync_cfg of None \<Rightarrow> True | Some bytes \<Rightarrow> supplier_abi_fixed 32 bytes) \<and>
         supplier_abi_u64 revision \<and> supplier_abi_fixed 32 mark_bytes \<and>
         supplier_abi_u64 quorum \<and> supplier_abi_octets statement_bytes
      then map_option (\<lambda>statement.
        \<lparr>supplier_selection_stores =
            \<lparr>supplier_journal_store = map nat_of_integer journal_id, supplier_witness_store = map nat_of_integer witness_id,
             supplier_terminal_authorities = map nat_of_integer terminal_cfg,
             supplier_commitment_authorities = map_option (map nat_of_integer) sync_cfg\<rparr>,
          supplier_selection_mark = (nat_of_integer revision,map nat_of_integer mark_bytes),
          supplier_selection_statement = statement,supplier_selection_quorum = nat_of_integer quorum\<rparr>)
        (supplier_decode_statement (map nat_of_integer statement_bytes))
      else None)"

definition supplier_abi_decode_vote ::
  "supplier_abi_vote \<Rightarrow> (wire_bytes, wire_bytes) supplier_vote option" where
  "supplier_abi_decode_vote input =
    (case input of (token,signer,signature) \<Rightarrow>
      if supplier_abi_u64 signer \<and> supplier_abi_fixed 64 signature then
        map_option (\<lambda>selected.
          \<lparr>supplier_vote_selection = selected,
           supplier_vote_signature = (nat_of_integer signer,map nat_of_integer signature)\<rparr>)
          (supplier_abi_decode_token token)
      else None)"

fun supplier_abi_traverse :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "supplier_abi_traverse decode [] = Some []"
| "supplier_abi_traverse decode (item # rest) =
    Option.bind (decode item) (\<lambda>parsed. map_option (Cons parsed) (supplier_abi_traverse decode rest))"

definition supplier_abi_aggregate ::
  "supplier_abi_token \<Rightarrow> supplier_abi_vote list \<Rightarrow> integer list option option" where
  "supplier_abi_aggregate token votes =
    Option.bind (supplier_abi_decode_token token) (\<lambda>selected.
      map_option (\<lambda>parsed. map_option (map integer_of_nat) (supplier_assemble_proof selected parsed))
        (supplier_abi_traverse supplier_abi_decode_vote votes))"

lemma supplier_abi_aggregate_uses_the_parent_decision_and_proof_bytes:
  assumes "supplier_abi_decode_token token = Some selected"
    "supplier_abi_traverse supplier_abi_decode_vote votes = Some parsed"
  shows "supplier_abi_aggregate token votes =
    Some (map_option (map integer_of_nat) (supplier_assemble_proof selected parsed))"
  using assms by (simp add: supplier_abi_aggregate_def)

definition supplier_abi_decode_record :: "supplier_abi_record \<Rightarrow> supplier_signed_record option" where
  "supplier_abi_decode_record input =
    (case input of (statement_bytes,issuer_signature) \<Rightarrow>
      if supplier_abi_octets statement_bytes \<and> supplier_abi_fixed 64 issuer_signature then
        Some \<lparr>supplier_record_statement = map nat_of_integer statement_bytes,
          supplier_record_signature = map nat_of_integer issuer_signature\<rparr>
      else None)"

type_synonym supplier_abi_tip_records = "sync_source_stream \<Rightarrow> supplier_signed_record option"

fun supplier_abi_replay_accepted ::
  "supplier_signed_record list \<Rightarrow> supplier_journal_view \<Rightarrow> supplier_abi_tip_records \<Rightarrow>
   (supplier_journal_view \<times> supplier_abi_tip_records) option" where
  "supplier_abi_replay_accepted [] view latest = Some (view,latest)"
| "supplier_abi_replay_accepted (signed_record # rest) view latest =
    Option.bind (supplier_decode_statement (supplier_record_statement signed_record)) (\<lambda>statement.
      Option.bind (supplier_extend_journal view statement) (\<lambda>updated.
        supplier_abi_replay_accepted rest updated (latest(sync_source_stream_of statement := Some signed_record))))"

definition supplier_abi_append_after_auth where
  "supplier_abi_append_after_auth view latest proposed statement =
    (case supplier_extend_journal view statement of
       Some _ \<Rightarrow> (0::integer)
     | None \<Rightarrow> if latest (sync_source_stream_of statement) = Some proposed then 1 else 2)"

definition supplier_abi_old_append ::
  "supplier_abi_token \<Rightarrow> supplier_abi_record list \<Rightarrow> supplier_abi_record \<Rightarrow> integer option" where
  "supplier_abi_old_append token prefix candidate =
    Option.bind (supplier_abi_decode_token token) (\<lambda>selected.
      Option.bind (supplier_abi_traverse supplier_abi_decode_record prefix) (\<lambda>retained.
        Option.bind (supplier_abi_decode_record candidate) (\<lambda>proposed.
          if proposed \<notin> set retained then None
          else Option.bind (supplier_abi_replay_accepted retained
            \<lparr>supplier_tips = (\<lambda>_. None),supplier_events = {}\<rparr> (\<lambda>_. None)) (\<lambda>(view,latest).
              Option.bind (supplier_decode_statement (supplier_record_statement proposed)) (\<lambda>statement.
                if supplier_tips view (sync_source_stream_of statement) = Some (supplier_selection_statement selected)
                then Some (supplier_abi_append_after_auth view latest proposed statement) else None)))))"

lemma supplier_abi_failed_append_only_uses_exact_current_signed_record_for_noop:
  assumes "supplier_extend_journal view statement = None"
  shows "supplier_abi_append_after_auth view latest proposed statement =
    (if latest (sync_source_stream_of statement) = Some proposed then 1 else 2)"
  using assms by (simp add: supplier_abi_append_after_auth_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms supplier_abi_sync_parse_votes_code
    supplier_abi_aggregate_uses_the_parent_decision_and_proof_bytes
    supplier_abi_failed_append_only_uses_exact_current_signed_record_for_noop})
  then () else error "Unexpected oracle in the SyncCommitment supplier ABI"
\<close>

export_code supplier_abi_aggregate supplier_abi_old_append
  in SML module_name OIP_Sync_Supplier_ABI file_prefix "oip_sync_supplier_abi"

end
