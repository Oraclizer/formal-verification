theory Replay_Export_ABI
  imports Replay_Export_Frames "HOL-Library.Code_Target_Nat"
begin

text \<open>The ABI receives decoded input words under the fixed typed fixture
contract. It uses equality of the entire typed request. The file decoder,
external signatures, and wire arrival storage are outside the model scope.\<close>

definition rpe_flag :: "bool \<Rightarrow> nat" where
  "rpe_flag value = (if value then 1 else 0)"

definition rpe_receipt ::
  "nat \<Rightarrow> nat \<Rightarrow> product_call_payload \<Rightarrow> rpf_state \<Rightarrow> authorized_receipt option" where
  "rpe_receipt mode input_epoch payload state =
    rpf_read (mode = 1 \<or> input_epoch = cut_authority_epoch (envelope_cut (payload_envelope payload)))
      (\<lambda>stored request. mode = 2 \<or> stored = request) input_epoch payload state"

lemma rpe_receipt_consumes_the_checked_projection:
  assumes "envelope_session (payload_envelope payload) \<in> set session_keys" "(7,1) \<in> set call_keys"
  shows "rpe_receipt mode input_epoch payload (rpf_project session_keys call_keys (prc_outcomes s)) =
    prc_read_with_tests (mode = 1 \<or> input_epoch = cut_authority_epoch (envelope_cut (payload_envelope payload)))
      (\<lambda>stored request. mode = 2 \<or> stored = request) input_epoch payload s"
  unfolding rpe_receipt_def by (rule rpf_reader_is_the_public_retained_receipt[OF assms])

fun rpe_outcome_tag :: "product_outcome \<Rightarrow> nat" where
  "rpe_outcome_tag (Authority_Reply (Protocol_Response Reservation_Acquired)) = 1"
| "rpe_outcome_tag (Authority_Reply (Protocol_Response Source_Dispatched)) = 2"
| "rpe_outcome_tag Authority_Rejected = 3"
| "rpe_outcome_tag Authority_Busy = 4"
| "rpe_outcome_tag Authority_Unavailable = 5"
| "rpe_outcome_tag other = 6"

fun rpe_receipt_words :: "authorized_receipt option \<Rightarrow> nat list" where
  "rpe_receipt_words None = [0,0]"
| "rpe_receipt_words (Some (Observed_Ordinary_Result Collection_Rejected)) = [1,0]"
| "rpe_receipt_words (Some (Observed_Ordinary_Result Collection_Waiting)) = [2,0]"
| "rpe_receipt_words (Some (Observed_Ordinary_Result (Collected reply))) = [3,rpe_outcome_tag reply]"
| "rpe_receipt_words other = [9,0]"

fun rpe_credential_words where
  "rpe_credential_words None = [0]"
| "rpe_credential_words (Some credential) =
    [1,token_asset (credential_token credential),fst (credential_origin credential),
      snd (credential_origin credential),token_owner (credential_token credential),
      token_generation (credential_token credential),credential_epoch credential]"

definition rpe_request_words where
  "rpe_request_words request =
    (let binding = request_binding request in
       [fst (binding_key binding),snd (binding_key binding),binding_asset binding,
        binding_destination binding,binding_recipient binding,binding_amount binding,
        binding_source_epoch binding,request_caller request,request_authority_epoch request,request_version request])"

fun rpe_command_words where
  "rpe_command_words (Client_Protocol endpoint index (Reserve_Intent request versions duration)) =
    [0,endpoint,index,duration,length versions] @ rpe_request_words request"
| "rpe_command_words (Client_Protocol endpoint index (Dispatch_Intent request generation versions)) =
    [1,endpoint,index,generation,length versions] @ rpe_request_words request"
| "rpe_command_words other = [2]"

definition rpe_payload_words where
  "rpe_payload_words payload =
    (let envelope = payload_envelope payload; payload_commit_cut = envelope_cut envelope in
      [envelope_message envelope,fst (envelope_origin envelope),snd (envelope_origin envelope),envelope_asset envelope,
       envelope_caller envelope,envelope_session envelope,cut_authority_epoch payload_commit_cut,cut_revision payload_commit_cut,payload_origin_epoch payload]
       @ rpe_credential_words (payload_credential payload) @ rpe_command_words (envelope_command envelope))"

fun rpe_session_words where
  "rpe_session_words None = [0,0,0]"
| "rpe_session_words (Some session) = [1,session_principal session,session_epoch session]"

definition rpe_entry_row where
  "rpe_entry_row state key =
    [3,fst key,snd key] @ (case map_of (rpf_entries state) key of None \<Rightarrow> [0]
      | Some (stored,ready) \<Rightarrow> [1,rpe_flag ready,rpe_outcome_tag (result_outcome stored)]
        @ rpe_payload_words (result_payload stored))"

definition rpe_frame_rows ::
  "rpf_state \<Rightarrow> nat \<Rightarrow> nat list list" where
  "rpe_frame_rows state input_session =
    [[1,rpf_epoch state,rpf_revision state,rpe_flag (rpf_live state),input_session]
      @ rpe_session_words (map_of (rpf_sessions state) input_session),
     rpe_entry_row state (7,1), rpe_entry_row state (7,2),
     [5,rpe_flag ((7,1) \<in> set (rpf_completed state)),rpe_flag ((7,2) \<in> set (rpf_completed state))]]"

definition rpe_receipt_rows ::
  "nat \<Rightarrow> nat \<Rightarrow> product_call_payload \<Rightarrow> rpf_state \<Rightarrow> nat list list" where
  "rpe_receipt_rows mode input_epoch payload state =
    (let response = rpe_receipt mode input_epoch payload state;
         exact = (case map_of (rpf_entries state) (7,1) of None \<Rightarrow> False
           | Some (stored,_) \<Rightarrow> result_payload stored = payload);
         epoch_ok = (input_epoch = cut_authority_epoch (envelope_cut (payload_envelope payload)))
     in [[0] @ rpe_receipt_words response,
         [2] @ rpe_payload_words payload,
         [4,rpe_flag epoch_ok,rpe_flag (rpf_identity input_epoch payload state),rpe_flag exact]]
        @ rpe_frame_rows state 1)"

definition rpe_active ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rpf_state \<Rightarrow> bool" where
  "rpe_active actor input_session input_epoch state =
    (input_epoch = rpf_epoch state \<and> map_of (rpf_sessions state) input_session =
      Some \<lparr>session_principal = actor, session_epoch = input_epoch\<rparr>)"

lemma rpe_projected_reader_is_the_typed_active_identity:
  assumes "input_session \<in> set session_keys"
  shows "rpe_active 7 input_session input_epoch (rpf_project session_keys call_keys outcomes) =
    active_identity identity_case_directory (identity_case_user 7) (identity_case_proof input_session input_epoch)
      (outcome_source outcomes)"
proof -
  have row: "map_of (rpf_sessions (rpf_project session_keys call_keys outcomes)) input_session =
    product_sessions (product_durable (outcome_source outcomes)) input_session"
    using assms by (simp add: rpf_project_def Let_def rpf_session_rows_def rpf_map_of_finite_rows)
  have epoch: "rpf_epoch (rpf_project session_keys call_keys outcomes) =
    cut_authority_epoch (current_product_cut (outcome_source outcomes))"
    by (simp add: rpf_project_def Let_def)
  show ?thesis
    unfolding rpe_active_def row epoch active_identity_def identity_case_directory_def identity_case_user_def identity_case_proof_def
    by simp
qed

definition rpe_read_rows ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> product_cut \<Rightarrow> nat \<Rightarrow> rpf_state \<Rightarrow> nat list list" where
  "rpe_read_rows op_tag actor input_session input_epoch expected position state =
    (let active = rpe_active actor input_session input_epoch state;
         result = (if \<not> active then [4]
           else if \<not> rpf_live state then [9]
           else if op_tag = 1 then
             (case native_current_read_value True id expected (rpf_epoch state) (rpf_revision state) rpe_prefix_units of
               None \<Rightarrow> [5] | Some (observed_commit_cut,value) \<Rightarrow> [7,cut_authority_epoch observed_commit_cut,cut_revision observed_commit_cut,value])
           else
             (case native_history_read_value True id position rpe_prefix_units of
               None \<Rightarrow> [6] | Some (selected,value) \<Rightarrow> [8,selected,value]))
     in [[0] @ result,[6,rpe_flag active,length rpe_prefix_units]] @ rpe_frame_rows state input_session)"

definition rpe_handover_rows ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "rpe_handover_rows op_tag route actor input_epoch signed_epoch =
    (let active = (input_epoch = rpe_handover_epoch \<and>
           rpe_old_session = Some \<lparr>session_principal = actor, session_epoch = input_epoch\<rparr>);
         signed = (signed_epoch = rpe_handover_epoch)
     in [[7,op_tag,route,rpe_flag (\<not> (active \<and> signed)),rpe_handover_epoch,
          (case rpe_new_owner of None \<Rightarrow> 0 | Some owner \<Rightarrow> owner)]
          @ rpe_session_words rpe_old_session])"

lemma rpe_handover_original_signed_epoch_refuses_each_actual_route:
  assumes "cut_authority_epoch (envelope_cut (payload_envelope payload)) = 9"
  shows "\<not> endpoint_call_allowed_on route directory policy authenticate verify token proof target operation actor call_id payload
    (hg_product_after True True)"
  by (rule prp_old_epoch_actions_after_handover_fail_every_route[OF assms])

fun rpe_observe_nat :: "nat list \<Rightarrow> nat list list" where
  "rpe_observe_nat [mode,setup,op_tag,route,target,actor,input_session,input_epoch,signed_epoch,signed_revision,sequence,duration,position] =
    (if mode > 2 \<or> route > 4 \<or> actor \<noteq> 7 \<or> input_session \<noteq> 1 then []
     else if setup = 2 then
       (if mode = 0 \<and> 3 \<le> op_tag \<and> op_tag \<le> 6 \<and> target = (if op_tag = 6 then 2 else 0)
          \<and> input_epoch = 9 \<and> signed_epoch = 9
        then rpe_handover_rows op_tag route actor input_epoch signed_epoch else [])
     else if setup > 1 \<or> target \<noteq> 0 then []
     else let state = (if setup = 0 then rpe_dispatch_frame else rpe_reopened_frame) in
       if op_tag = 0 \<and> sequence = 1 then rpe_receipt_rows mode input_epoch (rpe_payload signed_epoch signed_revision duration) state
       else if mode = 0 \<and> (op_tag = 1 \<or> op_tag = 2) \<and> (setup = 0 \<or> (op_tag = 2 \<and> input_epoch = 9)) then
         rpe_read_rows op_tag actor input_session input_epoch
           \<lparr>cut_authority_epoch = signed_epoch, cut_revision = signed_revision\<rparr> position state
       else [])"
| "rpe_observe_nat other = []"

definition rpe_u64 :: "integer \<Rightarrow> bool" where
  "rpe_u64 word \<longleftrightarrow> 0 \<le> word \<and> word < 18446744073709551616"

definition rpe_observe_integer where
  "rpe_observe_integer words =
    (if list_all rpe_u64 words
     then map (map integer_of_nat) (rpe_observe_nat (map nat_of_integer words))
     else [])"

thm_oracles rpe_receipt_consumes_the_checked_projection
  rpe_projected_reader_is_the_typed_active_identity rpe_handover_original_signed_epoch_refuses_each_actual_route

ML \<open>
  if null (Thm_Deps.all_oracles @{thms rpe_receipt_consumes_the_checked_projection
      rpe_projected_reader_is_the_typed_active_identity rpe_handover_original_signed_epoch_refuses_each_actual_route})
  then writeln "P13_REPLAY_EXPORT_ABI_ORACLES_EMPTY"
  else error "Unexpected oracle in replay export ABI"
\<close>

export_code rpe_observe_integer
  in SML module_name OIP_Replay_ABI file_prefix "oip_replay_abi"

end
