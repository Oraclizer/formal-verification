theory Primary_Origin_Export
  imports "OIP_Primary_Origin_Check.Primary_Origin_Check"
begin

fun po_binding_from_words where
  "po_binding_from_words [po_domain,po_event,po_asset,po_owner,po_target,po_recipient,po_amount,po_source_epoch,po_separator] =
    Some (\<lparr>binding_key = (po_domain,po_event), binding_asset = po_asset, binding_amount = po_amount,
      binding_destination = po_target, binding_recipient = po_recipient,
      binding_source_epoch = po_source_epoch, binding_operation = Destination_Credit,
      binding_separator = po_separator\<rparr>, po_owner)"
| "po_binding_from_words _ = None"

fun po_bit where
  "po_bit False = (0::nat)"
| "po_bit True = 1"

definition po_optional where
  "po_optional po_flag po_value = (if po_flag = (1::nat) then Some po_value else None)"

definition po_commands where
  "po_commands (po_tag::nat) po_record_binding po_kind po_ref = map_of
    [(0,(PO_Debit,Native_Other)),
     (1,(PO_Terminal po_record_binding po_kind,Native_Record (fst po_record_binding,po_kind,po_ref))),
     (2,(PO_Confirm,Native_Credit po_ref)),
     (3,(PO_Reverse,Native_Refund po_ref)),
     (4,(PO_Confirm,Native_Other)),
     (5,(PO_Publish,Native_Publish))] po_tag"

fun po_duplicate_words where
  "po_duplicate_words None = [0,0]"
| "po_duplicate_words (Some (Native_Decision po_commit)) = [1,po_commit]"
| "po_duplicate_words (Some (Native_Settlement po_kind po_commit)) = [if po_kind then 2 else 3,po_commit]"
| "po_duplicate_words (Some (Native_Published po_commit)) = [4,po_commit]"

definition po_duplicate_input where
  "po_duplicate_input po_requested po_native_cmd po_row po_record =
    \<lparr>duplicate_binding_value = fst po_requested,
     duplicate_command_value = po_native_cmd,
     duplicate_origins_value = (\<lambda>po_key. if po_key = binding_key (fst po_requested)
       then map_option po_retained_values po_row else None),
     duplicate_evidence_value = (\<lambda>po_ref. Option.bind po_record (\<lambda>(po_evidence,po_kind,po_index).
       if po_ref = po_index \<and> snd po_evidence = snd po_requested
       then Some (fst po_evidence,po_kind,po_index) else None))\<rparr>"

definition po_selection_words where
  "po_selection_words check_epoch po_requested po_epoch po_cut po_cmd po_native_cmd po_row po_record =
    (let po_allowed = po_origin_allowed check_epoch po_requested po_epoch po_cut po_cmd po_row in
       [po_bit po_allowed] @ po_duplicate_words
         (if po_allowed then native_duplicate_selected_value
            (po_duplicate_input po_requested po_native_cmd po_row po_record) else None))"

lemma po_rejected_slot_never_supplies_a_duplicate:
  "\<not> po_origin_allowed check_epoch po_requested po_epoch po_cut po_cmd po_row \<Longrightarrow>
    po_selection_words check_epoch po_requested po_epoch po_cut po_cmd po_native_cmd po_row po_record = [0,0,0]"
  by (simp add: po_selection_words_def Let_def)

definition po_observe where
  "po_observe po_header po_request_words po_slot_words po_record_words po_evidence_words =
    (case po_header of
       [po_tag,po_epoch,po_cut,po_kind,po_ref,po_present,po_stored_epoch,po_debit,
        po_decision,po_decision_kind,po_decision_commit,po_settled,po_settlement_position,
        po_published,po_publication_position,po_evidence_present,po_evidence_kind,po_evidence_ref] \<Rightarrow>
        (if \<not> list_all (\<lambda>po_flag. po_flag \<le> 1)
          [po_kind,po_present,po_decision,po_decision_kind,po_settled,po_published,po_evidence_present,po_evidence_kind] then None else
        Option.bind (po_binding_from_words po_request_words) (\<lambda>po_requested.
        Option.bind (po_binding_from_words po_slot_words) (\<lambda>po_stored.
        Option.bind (po_binding_from_words po_record_words) (\<lambda>po_record_binding.
        Option.bind (po_binding_from_words po_evidence_words) (\<lambda>po_evidence.
        Option.bind (po_commands po_tag po_record_binding (po_kind = 1) po_ref) (\<lambda>(po_cmd,po_native_cmd).
          let po_values = \<lparr>slot_decision_value = po_optional po_decision (po_decision_kind = 1,po_decision_commit),
                            slot_settlement_value = po_optional po_settled po_settlement_position,
                            slot_publication_value = po_optional po_published po_publication_position\<rparr>;
              po_row = po_optional po_present \<lparr>po_retained_binding = po_stored, po_retained_epoch = po_stored_epoch,
                  po_retained_debit = po_debit, po_retained_values = po_values\<rparr>;
              po_record = po_optional po_evidence_present (po_evidence,po_evidence_kind = 1,po_evidence_ref)
          in Some (po_selection_words True po_requested po_epoch po_cut po_cmd po_native_cmd po_row po_record @
              po_selection_words False po_requested po_epoch po_cut po_cmd po_native_cmd po_row po_record)))))))
      | _ \<Rightarrow> None)"

definition po_observe_integer :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "po_observe_integer po_header po_requested po_stored po_record po_evidence =
    (if list_all (\<lambda>po_word. 0 \<le> po_word) (po_header @ po_requested @ po_stored @ po_record @ po_evidence) then
       map_option (map integer_of_nat) (po_observe (map nat_of_integer po_header) (map nat_of_integer po_requested)
           (map nat_of_integer po_stored) (map nat_of_integer po_record) (map nat_of_integer po_evidence))
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms po_rejected_slot_never_supplies_a_duplicate}) then ()
  else error "Unexpected oracle in primary origin export"
\<close>

export_code po_observe_integer in SML module_name OIP_Primary_Origin file_prefix "oip_primary_origin"

end
