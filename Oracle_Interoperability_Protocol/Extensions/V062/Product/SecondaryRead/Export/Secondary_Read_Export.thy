theory Secondary_Read_Export
  imports "OIP_Secondary_Read_G0.Secondary_Read_G0" "HOL-Library.Code_Target_Nat"
begin

definition secondary_export_slot :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list secondary_slot option" where
  "secondary_export_slot present_input decision_input published_input payload_input =
    (if present_input = 0 then None else Some
      \<lparr>secondary_slot_terminal = (if decision_input = 0 then None else Some payload_input),
       secondary_slot_publication = (published_input = 1)\<rparr>)"

fun secondary_export_terminal :: "(nat list,nat list) secondary_terminal option \<Rightarrow> nat list" where
  "secondary_export_terminal None = [0,0]"
| "secondary_export_terminal (Some (Secondary_Transfer payload_input)) = [1,length payload_input] @ payload_input"
| "secondary_export_terminal (Some (Secondary_Legal payload_input)) = [2,length payload_input] @ payload_input"

fun secondary_export_status_fields :: "(nat,nat list,nat list) secondary_status_view secondary_read_reply \<Rightarrow> nat list" where
  "secondary_export_status_fields Secondary_Rejected = [0,0,0,0,0,0,0]"
| "secondary_export_status_fields Secondary_Unavailable = [1,0,0,0,0,0,0]"
| "secondary_export_status_fields (Secondary_Answer answer_input) =
    [2] @ (case secondary_status_phase answer_input of None \<Rightarrow> [0,0] | Some phase_input \<Rightarrow> [1,phase_input]) @
    [secondary_status_pending answer_input,(if secondary_status_published answer_input then 1 else 0)] @
    secondary_export_terminal (secondary_status_terminal answer_input)"

fun secondary_export_status_nat :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list option" where
  "secondary_export_status_nat [row_id,authorized_input,available_input,target_input,domain_input,event_input,
     phase_present,phase_input,pending_input,transfer_present,transfer_decision,transfer_published,
     legal_present,legal_decision,legal_published] transfer_payload legal_payload =
    (if \<not> list_all (\<lambda>n. n \<le> 1)
       [authorized_input,available_input,phase_present,transfer_present,transfer_decision,transfer_published,
        legal_present,legal_decision,legal_published] then None
     else Some ([row_id,target_input,domain_input,event_input] @
       secondary_export_status_fields (secondary_status (authorized_input = 1) (available_input = 1)
         target_input (domain_input,event_input) (if phase_present = 1 then Some phase_input else None) pending_input
         (secondary_export_slot transfer_present transfer_decision transfer_published transfer_payload)
         (secondary_export_slot legal_present legal_decision legal_published legal_payload))))"
| "secondary_export_status_nat _ transfer_payload legal_payload = None"

definition secondary_export_status :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "secondary_export_status metadata transfer_payload legal_payload =
    (if list_all (\<lambda>n. 0 \<le> n) (metadata @ transfer_payload @ legal_payload)
     then map_option (map integer_of_nat) (secondary_export_status_nat
       (map nat_of_integer metadata) (map nat_of_integer transfer_payload) (map nat_of_integer legal_payload)) else None)"

fun secondary_export_journal_rows :: "nat list \<Rightarrow> secondary_journal_item list option" where
  "secondary_export_journal_rows [] = Some []"
| "secondary_export_journal_rows (namespace_input # sequence_input # target_input # commit_input # rest_input) =
    map_option (\<lambda>tail_input. secondary_g0_journal_item namespace_input sequence_input target_input commit_input # tail_input)
      (secondary_export_journal_rows rest_input)"
| "secondary_export_journal_rows _ = None"

definition secondary_export_ids where
  "secondary_export_ids ids = [length ids] @ concat (map (\<lambda>call_id. [fst call_id,snd call_id]) ids)"

fun secondary_export_journal_nat :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list option" where
  "secondary_export_journal_nat [row_id,namespace_input,target_input,live_revision] row_fields =
    map_option (\<lambda>journal_rows. [row_id,namespace_input,target_input,live_revision] @
      secondary_export_ids (secondary_journal namespace_input target_input live_revision journal_rows) @
      secondary_export_ids (secondary_journal_nonstrict namespace_input target_input live_revision journal_rows))
      (secondary_export_journal_rows row_fields)"
| "secondary_export_journal_nat _ row_fields = None"

definition secondary_export_journal :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "secondary_export_journal metadata row_fields =
    (if list_all (\<lambda>n. 0 \<le> n) (metadata @ row_fields) then map_option (map integer_of_nat)
       (secondary_export_journal_nat (map nat_of_integer metadata) (map nat_of_integer row_fields)) else None)"

fun secondary_export_raw_rows :: "nat list \<Rightarrow> (nat option \<times> bool) list option" where
  "secondary_export_raw_rows [] = Some []"
| "secondary_export_raw_rows (present_input # units_input # locked_input # rest_input) =
    (if present_input > 1 \<or> locked_input > 1 then None else
      map_option (\<lambda>tail_input. ((if present_input = 1 then Some units_input else None),locked_input = 1) # tail_input)
        (secondary_export_raw_rows rest_input))"
| "secondary_export_raw_rows _ = None"

fun secondary_export_raw_nat :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list option" where
  "secondary_export_raw_nat [row_id,selected_revision,current_revision] row_fields =
    (case secondary_export_raw_rows row_fields of None \<Rightarrow> None | Some prefixes \<Rightarrow>
      if selected_revision \<noteq> current_revision \<or> length prefixes \<noteq> Suc current_revision then None
      else Some ([row_id,current_revision,selected_revision,(if snd (prefixes ! selected_revision) then 1 else 0)] @
        (case secondary_raw_application selected_revision prefixes of None \<Rightarrow> [0,0] | Some units_input \<Rightarrow> [1,units_input])))"
| "secondary_export_raw_nat _ row_fields = None"

definition secondary_export_raw :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "secondary_export_raw metadata row_fields =
    (if list_all (\<lambda>n. 0 \<le> n) (metadata @ row_fields) then map_option (map integer_of_nat)
       (secondary_export_raw_nat (map nat_of_integer metadata) (map nat_of_integer row_fields)) else None)"

fun secondary_export_registry :: "nat list \<Rightarrow> (nat \<times> nat) list option" where
  "secondary_export_registry [] = Some []"
| "secondary_export_registry (asset_input # owner_input # rest_input) =
    map_option (\<lambda>tail_input. (asset_input,owner_input) # tail_input) (secondary_export_registry rest_input)"
| "secondary_export_registry _ = None"

fun secondary_export_owner_nat :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list option" where
  "secondary_export_owner_nat [row_id,asset_input] registry_fields =
    (case secondary_export_registry registry_fields of None \<Rightarrow> None | Some registry_input \<Rightarrow>
      if \<not> distinct (map fst registry_input) then None else Some ([row_id,asset_input] @
        (case secondary_owner_registry registry_input asset_input of None \<Rightarrow> [0,0] | Some owner_input \<Rightarrow> [1,owner_input])))"
| "secondary_export_owner_nat _ registry_fields = None"

definition secondary_export_owner :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "secondary_export_owner metadata registry_fields =
    (if list_all (\<lambda>n. 0 \<le> n) (metadata @ registry_fields) then map_option (map integer_of_nat)
       (secondary_export_owner_nat (map nat_of_integer metadata) (map nat_of_integer registry_fields)) else None)"

fun secondary_export_selector_fields :: "nat retained_service_action option \<Rightarrow> nat list option" where
  "secondary_export_selector_fields (Some (Service_Read token_input proof_input target_input (Raw_Data (Application_Value asset_input)) None)) =
    Some [3,proof_session proof_input,proof_epoch proof_input,target_input,1,asset_input,0,0]"
| "secondary_export_selector_fields (Some (Service_Read token_input proof_input target_input (Operation_Status (domain_input,event_input)) None)) =
    Some [4,proof_session proof_input,proof_epoch proof_input,target_input,0,0,domain_input,event_input]"
| "secondary_export_selector_fields (Some (Service_Read token_input proof_input target_input Authority_Journal None)) =
    Some [5,proof_session proof_input,proof_epoch proof_input,target_input,0,0,0,0]"
| "secondary_export_selector_fields (Some (Service_Read token_input proof_input target_input (Owner_Data asset_input) None)) =
    Some [7,proof_session proof_input,proof_epoch proof_input,target_input,0,asset_input,0,0]"
| "secondary_export_selector_fields _ = None"

definition secondary_export_decode :: "integer list \<Rightarrow> integer list option" where
  "secondary_export_decode integer_bytes =
    (if \<not> list_all (\<lambda>n. 0 \<le> n \<and> n < 256) integer_bytes then None
     else let input_bytes = map nat_of_integer integer_bytes in
       case decode_wire_packet input_bytes of None \<Rightarrow> None | Some packet_input \<Rightarrow>
         if encode_wire_packet packet_input \<noteq> input_bytes then None else
         let core_input = packet_core packet_input in
         map_option (\<lambda>fields_input. map integer_of_nat
           ([wire_principal core_input,wire_key_number core_input,wire_source_domain core_input,wire_deployment core_input] @ fields_input))
           (secondary_export_selector_fields (code_source_nonreceipt_read_service (0::nat) core_input)))"

text \<open>The decoder does not check a signature, token, TTL, grant or product target.\<close>

export_code secondary_export_decode secondary_export_status secondary_export_journal
  secondary_export_raw secondary_export_owner
  in SML module_name OIP_Secondary_Read file_prefix "oip_secondary_read"

end
