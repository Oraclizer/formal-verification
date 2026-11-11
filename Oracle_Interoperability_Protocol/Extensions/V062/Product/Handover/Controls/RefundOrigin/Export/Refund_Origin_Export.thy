theory Refund_Origin_Export
  imports "OIP_V062_Refund_Origin_Link.Refund_Origin_Link"
    "HOL-Library.Code_Target_Nat"
begin

text \<open>
  A bounded projection for the fresh Refund in the supplied pending case.
  The selected certificate, its authentication, the active session and the
  current owner come from separate observations. The logical terminal lookup
  uses the exact supplied wire reference. Retained reads use Completion_Gates.
\<close>

definition ror_native_observation where
  "ror_native_observation (stage :: nat) retained financial =
    [stage, (if native_origin_pending financial then binding_amount (fst retained) else 0),
     native_available_source financial, native_funded_destination financial,
     (if native_origin_owns_footprint financial then 1 else 0)]"

definition ror_native_fresh_refund where
  "ror_native_fresh_refund owned financial clock lease_end selected_ref selected_kind retained
     decided_epoch requested_ref request_epoch current_owner endorser =
    (let frame = ror_native_observation
     in if selected_ref \<noteq> requested_ref \<or> selected_kind \<noteq> Native_Reverse
          then frame 1 owned financial
        else if current_owner \<noteq> endorser then frame 2 owned financial
        else if tr_first_reference retained = None \<or> decided_epoch \<noteq> request_epoch
          then frame 3 owned financial
        else let (after,accepted) = tr_settlement_effect False retained owned requested_ref Native_Reverse
               clock lease_end financial
             in frame (if accepted then 5 else 4) owned after)"

lemma ror_native_refund_requires_exact_evidence:
  assumes "selected_ref = requested_ref" "current_owner = endorser"
    "tr_first_reference retained \<noteq> None" "decided_epoch = request_epoch"
    "map_of (tr_evidence_rows retained) requested_ref = None"
  shows "ror_native_fresh_refund owned financial clock lease_end selected_ref Native_Reverse retained
      decided_epoch requested_ref request_epoch current_owner endorser = ror_native_observation 4 owned financial"
proof -
  obtain first_ref where first: "tr_first_reference retained = Some first_ref"
    using assms(3) by (cases "tr_first_reference retained") auto
  have no_settlement: "tr_settlement_effect False retained owned requested_ref Native_Reverse
      clock lease_end financial = (financial, False)"
    by (rule tr_missing_requested_reference_cannot_move_funds[OF assms(5)])
  show ?thesis
    using assms(1,2,4) first no_settlement
    by (simp add: ror_native_fresh_refund_def Let_def)
qed

definition ror_finite_words where
  "ror_finite_words metadata = (case metadata of
    [source_domain,event,asset,destination,recipient,funding_owner,amount,initial,source_epoch,
     current_owner,endorser,decided_epoch,requested_epoch,selected_kind,selected_ref,requested_ref,
     recorded,clock,lease_end] \<Rightarrow>
       if amount = 0 \<or> initial < amount \<or> selected_kind \<notin> {1,2} \<or> recorded > 1 then None else
       let kind = (if selected_kind = 2 then Native_Reverse else Native_Confirm);
           owned = (\<lparr>binding_key = (source_domain,event), binding_asset = asset, binding_amount = amount,
                     binding_destination = destination, binding_recipient = recipient,
                     binding_source_epoch = source_epoch, binding_operation = Destination_Credit,
                     binding_separator = 0\<rparr>, funding_owner);
           before = \<lparr>native_origin_pending = True, native_funded_destination = 0,
                     native_root_lot = 0, native_available_source = initial - amount,
                     native_origin_owns_footprint = True\<rparr>;
           empty = \<lparr>tr_first_reference = None, tr_evidence_rows = []\<rparr>;
           retained = (if recorded = 1 then fst (tr_record_evidence True owned selected_ref (owned,kind) empty)
             else empty)
       in Some (ror_native_fresh_refund owned before clock lease_end selected_ref kind retained
           decided_epoch requested_ref requested_epoch current_owner endorser)
    | _ \<Rightarrow> None)"

definition ror_export_words :: "integer list \<Rightarrow> integer list option" where
  "ror_export_words words =
    (if list_all (\<lambda>word. 0 \<le> word \<and> word < 18446744073709551616) words
     then map_option (map integer_of_nat) (ror_finite_words (map nat_of_integer words)) else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ror_native_refund_requires_exact_evidence})
  then () else error "Unexpected oracle in the projected Refund guard"
\<close>

code_reserved (SML) before

export_code ror_export_words in SML module_name OIP_Refund_Origin file_prefix "oip_refund_origin"

end
