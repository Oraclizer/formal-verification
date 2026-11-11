theory Terminal_Record_Export
  imports "OIP_Terminal_Record_G0.Terminal_Record_G0" "HOL-Library.Code_Target_Nat"
begin

datatype tr_stimulus = TR_Evidence nat native_terminal_path nat | TR_Credit nat | TR_Refund nat

fun tr_kind_word where
  "tr_kind_word Native_Confirm = 1"
| "tr_kind_word Native_Reverse = 2"

fun tr_record_reply_word where
  "tr_record_reply_word TR_Record_Rejected = 0"
| "tr_record_reply_word TR_First_Record = 1"
| "tr_record_reply_word TR_Refreshed_Record = 2"

definition tr_parse_stimulus :: "nat list \<Rightarrow> tr_stimulus option" where
  "tr_parse_stimulus raw = (case raw of
      [action_tag,requested,kind_word,owner] \<Rightarrow>
        if action_tag \<noteq> 1 then None
        else if kind_word = 1 then Some (TR_Evidence requested Native_Confirm owner)
        else if kind_word = 2 then Some (TR_Evidence requested Native_Reverse owner) else None
    | [action_tag,requested] \<Rightarrow> if action_tag = 2 then Some (TR_Credit requested)
        else if action_tag = 3 then Some (TR_Refund requested) else None
    | _ \<Rightarrow> None)"

fun tr_export_step where
  "tr_export_step fallback owned current_time lease_end (TR_Evidence requested kind owner) (retained,financial) =
    (let (updated,reply) = tr_record_evidence (native_origin_pending financial) owned requested
        ((fst owned,owner),kind) retained
     in ((updated,financial),tr_record_reply_word reply))"
| "tr_export_step fallback owned current_time lease_end (TR_Credit requested) (retained,financial) =
    (let (updated,accepted) = tr_settlement_effect fallback retained owned requested Native_Confirm current_time lease_end financial
     in ((retained,updated),if accepted then 3 else 0))"
| "tr_export_step fallback owned current_time lease_end (TR_Refund requested) (retained,financial) =
    (let (updated,accepted) = tr_settlement_effect fallback retained owned requested Native_Reverse current_time lease_end financial
     in ((retained,updated),if accepted then 4 else 0))"

definition tr_export_view where
  "tr_export_view result =
    (let (retained,financial) = fst result;
         first_ref = (case tr_first_reference retained of None \<Rightarrow> [0,0] | Some reference \<Rightarrow> [1,reference]);
         evidence = concat (map (\<lambda>(reference,(binding,kind)). [reference,tr_kind_word kind,snd binding])
                             (tr_evidence_rows retained))
     in [snd result] @ first_ref @ [length (tr_evidence_rows retained),
        (if native_origin_pending financial then 1 else 0),native_available_source financial,
        native_funded_destination financial,native_root_lot financial,
        (if native_origin_owns_footprint financial then 1 else 0)] @ evidence)"

fun tr_export_trace where
  "tr_export_trace fallback owned current_time lease_end [] before = Some []"
| "tr_export_trace fallback owned current_time lease_end (raw # remaining) before =
    (case tr_parse_stimulus raw of None \<Rightarrow> None | Some stimulus \<Rightarrow>
      let result = tr_export_step fallback owned current_time lease_end stimulus before
      in case tr_export_trace fallback owned current_time lease_end remaining (fst result) of
        None \<Rightarrow> None | Some later \<Rightarrow> Some (tr_export_view result # later))"

definition tr_run_case where
  "tr_run_case fallback metadata actions = (case metadata of
      [source_domain,event,asset,destination,recipient,owner,amount,epoch,initial,current_time,lease_end] \<Rightarrow>
       if initial < amount then None else
       let binding = \<lparr>binding_key = (source_domain,event), binding_asset = asset, binding_amount = amount,
                      binding_destination = destination, binding_recipient = recipient, binding_source_epoch = epoch,
                      binding_operation = Destination_Credit,binding_separator = 0\<rparr>;
           before = (\<lparr>tr_first_reference = None,tr_evidence_rows = []\<rparr>,
                     \<lparr>native_origin_pending = True,native_funded_destination = 0,native_root_lot = 0,
                       native_available_source = initial - amount,native_origin_owns_footprint = True\<rparr>)
       in tr_export_trace fallback (binding,owner) current_time lease_end actions before
    | _ \<Rightarrow> None)"

definition tr_u64_words :: "integer list \<Rightarrow> bool" where
  "tr_u64_words words = list_all (\<lambda>word. 0 \<le> word \<and> word < 18446744073709551616) words"

definition tr_export_integer_trace where
  "tr_export_integer_trace fallback metadata actions =
    (if tr_u64_words metadata \<and> list_all tr_u64_words actions then
       map_option (map (map integer_of_nat))
          (tr_run_case fallback (map nat_of_integer metadata) (map (map nat_of_integer) actions))
     else None)"

definition tr_export_identity :: "integer list" where
  "tr_export_identity = [1,64,11,9]"

text \<open>
  The standalone reader checks the exact input order and requires one observed
  row for every stimulus in the frozen finite corpus.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms tr_refresh_keeps_primary_and_binds_the_exact_new_reference
    tr_removing_only_missing_reference_refusal_can_admit_credit})
  then () else error "Unexpected oracle in typed terminal evidence export"
\<close>

code_reserved (SML) before

export_code tr_export_integer_trace tr_export_identity
  in SML module_name OIP_Terminal_Record file_prefix "oip_terminal_record"

end
