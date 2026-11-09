theory Sync_V061_Attestation_Model
  imports "OIP_Sync_V061_Wire_V4.Sync_V061_Wire"
    "OIP_Reference_Profile.Reference_Source_Freshness"
begin

type_synonym sync_stream = "product_asset \<times> nat"
type_synonym sync_votes = "(nat \<times> wire_bytes) list"
type_synonym 'key sync_verify = "'key \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool"

datatype sync_mode = Sync_Initial | Sync_Incremental | Sync_Full

record sync_entry =
  sync_commitment :: wire_bytes
  sync_position :: nat
  sync_origin_epoch :: nat
  sync_event :: nat

record sync_statement =
  sync_format :: nat
  sync_claim :: nat
  sync_deployment :: nat
  sync_origin :: nat
  sync_roster :: nat
  sync_asset :: product_asset
  sync_item :: sync_entry
  sync_predecessor :: "wire_bytes option"

abbreviation sync_word where "sync_word n \<equiv> rev (put_le_octets 8 n)"
abbreviation sync_take_word where "sync_take_word bs \<equiv> get_le_octets (rev (take 8 bs))"
abbreviation sync_domain :: wire_bytes where
  "sync_domain \<equiv> [79,73,80,0,83,79,85,82,67,69,45,65,84,84,69,83,84,65,84,73,79,78,0]"

definition sync_statement_bytes where
  "sync_statement_bytes a =
    sync_domain @ concat (map sync_word [sync_format a, sync_claim a, sync_deployment a, sync_origin a,
      sync_origin_epoch (sync_item a), sync_roster a, sync_asset a, sync_event (sync_item a), sync_position (sync_item a)]) @
    sync_commitment (sync_item a) @ (case sync_predecessor a of None \<Rightarrow> [0] | Some prior \<Rightarrow> 1 # prior)"

definition sync_proof_bytes where
  "sync_proof_bytes a votes = sync_statement_bytes a @ sync_word (length votes) @
    concat (map (\<lambda>(signer, signature). sync_word signer @ signature) votes)"

fun sync_parse_votes :: "nat \<Rightarrow> wire_bytes \<Rightarrow> sync_votes" where
  "sync_parse_votes 0 raw = []"
| "sync_parse_votes (Suc n) raw =
    (sync_take_word raw, take 64 (drop 8 raw)) # sync_parse_votes n (drop 72 raw)"

definition sync_parse_proof where
  "sync_parse_proof raw =
    (let payload = drop (length sync_domain) raw; word = (\<lambda>i. sync_take_word (drop (8 * i) payload)) in
     case drop 104 payload of [] \<Rightarrow> None
     | presence # rest \<Rightarrow>
        let width = (if presence = 0 then 0 else 32); tail = drop width rest; count = sync_take_word tail;
            a = \<lparr>sync_format = word 0, sync_claim = word 1, sync_deployment = word 2, sync_origin = word 3,
                 sync_roster = word 5, sync_asset = word 6,
                 sync_item = \<lparr>sync_commitment = take 32 (drop 72 payload), sync_position = word 8,
                    sync_origin_epoch = word 4, sync_event = word 7\<rparr>,
                 sync_predecessor = (if presence = 0 then None else Some (take width rest))\<rparr>
        in if presence \<le> 1 \<and> length tail = 8 + 72 * count
           then Some (a, sync_parse_votes count (drop 8 tail)) else None)"

definition sync_decode_proof where
  "sync_decode_proof = code_reencoding_decode wire_octets sync_parse_proof
    (\<lambda>(a,votes). Some (sync_proof_bytes a votes))"

record sync_request =
  sync_call :: client_call_id
  sync_message :: nat
  sync_session :: product_session_id
  sync_signed_cut :: product_cut
  sync_key :: sync_stream
  sync_requested :: sync_entry
  sync_mode :: sync_mode
  sync_claimed_prior :: "wire_bytes option"
  sync_attestation :: wire_bytes

definition sync_mode_at :: "nat \<Rightarrow> sync_mode option" where
  "sync_mode_at tag =
    (if tag = 1 then Some Sync_Initial else if tag = 2 then Some Sync_Incremental
     else if tag = 3 then Some Sync_Full else None)"

definition sync_read_operands where
  "sync_read_operands core =
    (let body = wire_operation_body core in
     if wire_message_family core \<noteq> Wire_State_Sync \<or> wire_opcode body \<noteq> 7 \<or>
        wire_deadline body \<noteq> Deadline_Absent then None else
     case (wire_words body, wire_blobs body) of
       ([message,call_sequence,session,revision_word,epoch,origin,event,asset,pos,mode],[commitment,prior,proof]) \<Rightarrow>
        Option.bind (sync_mode_at mode) (\<lambda>m.
          if length commitment = 32 \<and> length prior = (if m = Sync_Incremental then 32 else 0)
          then Some \<lparr>sync_call = (wire_principal core,call_sequence), sync_message = message, sync_session = session,
            sync_signed_cut = \<lparr>cut_authority_epoch = wire_authority_epoch core, cut_revision = revision_word\<rparr>,
            sync_key = (asset,origin),
            sync_requested = \<lparr>sync_commitment = commitment, sync_position = pos, sync_origin_epoch = epoch, sync_event = event\<rparr>,
            sync_mode = m, sync_claimed_prior = (if m = Sync_Incremental then Some prior else None),
            sync_attestation = proof\<rparr> else None)
     | _ \<Rightarrow> None)"

record 'key sync_registry =
  sync_current_roster :: "nat \<Rightarrow> (nat \<times> nat) option"
  sync_registered_rosters :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> (nat \<Rightarrow> 'key option)) option"

definition sync_proof_ok :: "'key sync_verify \<Rightarrow> 'key sync_registry \<Rightarrow> wire_core \<Rightarrow> sync_request \<Rightarrow>
  sync_statement \<Rightarrow> sync_votes \<Rightarrow> bool" where
  "sync_proof_ok verify registry core r a votes \<longleftrightarrow>
    sync_format a = 1 \<and> sync_claim a = 1 \<and> sync_deployment a = wire_deployment core \<and>
    (sync_asset a, sync_origin a) = sync_key r \<and> sync_item a = sync_requested r \<and>
    sync_predecessor a = sync_claimed_prior r \<and>
    sync_current_roster registry (sync_origin a) = Some (sync_origin_epoch (sync_item a), sync_roster a) \<and>
    (case sync_registered_rosters registry (sync_deployment a,sync_origin a,sync_origin_epoch (sync_item a),sync_roster a) of
      None \<Rightarrow> False | Some (quorum, keys) \<Rightarrow> 0 < quorum \<and> quorum \<le> length votes \<and>
        sorted_wrt (<) (map fst votes) \<and> distinct (map (keys \<circ> fst) votes) \<and>
        (\<forall>(signer,signature) \<in> set votes. \<exists>key.
          keys signer = Some key \<and> verify key (sync_statement_bytes a) signature))"

end
