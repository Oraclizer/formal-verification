theory Signed_Schedule_Refusals
  imports "OIP_Signed_Schedule_Pair.Signed_Schedule_Pair"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen"
begin

section \<open>Per-occurrence refusal and selected-neighbor effects\<close>

text \<open>
  Scope: version six, the two frozen single-signature packet roles and a
  stable ordered cut. The model runs the existing canonical decoder and
  admission rules. Ed25519 verification, the configured allowlist and the
  credential equality gate enter at their source boundaries. After successful
  signature verification only the exact seeded ACK and current read are
  projected. Authorization and product agreement for those retained fixture
  calls, successful revalidation and successful head confirmation are explicit
  premises of the differential observation. Pending is separate from refusal.
\<close>

definition ssr_in_schedule where
  "ssr_in_schedule core \<longleftrightarrow>
    wire_opcode (wire_operation_body core) = 1 \<and>
    wire_message_family core \<in> {Wire_Ack, Wire_Query}"

definition ssr_shape :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> wire_bytes
    \<Rightarrow> (wire_refusal + wire_packet) option" where
  "ssr_shape version frame_limit configured raw =
    (if version \<noteq> 6 then Some (Inl Unsupported_Wire_Version)
     else case code_check_declared_version raw frame_limit of
       Some error \<Rightarrow> Some (Inl error)
     | None \<Rightarrow> (case decode_wire_packet raw of
         None \<Rightarrow> Some (Inl Invalid_Wire_Format)
       | Some packet \<Rightarrow> if \<not> configured then Some (Inl Unsupported_Wire_Version)
         else (case code_transport_operand_verdict (packet_core packet) 1 of
           Code_Operand_Pending \<Rightarrow> None
         | Code_Operand_Refuse error \<Rightarrow> Some (Inl error)
         | Code_Operand_Accept \<Rightarrow>
           if ssr_in_schedule (packet_core packet) then Some (Inr packet)
           else Some (Inl Invalid_Wire_Format))))"

record ssr_lane =
  srl_label :: nat
  srl_boundary :: wire_boundary
  srl_nesting :: nat
  srl_configured :: bool
  srl_credentials_match :: bool
  srl_signature_valid :: bool
  srl_reference :: wire_bytes
  srl_raw :: wire_bytes

datatype ssr_result =
    SSR_Shape_Refused wire_refusal
  | SSR_Consume_Refused wire_refusal
  | SSR_Pending
  | SSR_Selected bool wire_bytes

definition ssr_lane_shape where
  "ssr_lane_shape lane = ssr_shape
     (negotiated_version (boundary_profile (srl_boundary lane)))
     (boundary_max_frame (srl_boundary lane)) (srl_configured lane) (srl_raw lane)"

definition ssr_observe where
  "ssr_observe lane prior =
    (case ssr_lane_shape lane of
       None \<Rightarrow> SSR_Pending
     | Some (Inl error) \<Rightarrow> SSR_Shape_Refused error
     | Some (Inr packet) \<Rightarrow>
       if \<not> srl_credentials_match lane then SSR_Consume_Refused Invalid_Wire_Signature
       else (case code_admit_packet (\<lambda>_ _ _. srl_signature_valid lane) packet (srl_boundary lane) of
         Some error \<Rightarrow> SSR_Consume_Refused error
       | None \<Rightarrow> if srl_raw lane \<noteq> srl_reference lane then SSR_Pending
         else let exact = encode_wire_core (packet_core packet) in
           (case code_compare_binding prior exact of
              Code_First \<Rightarrow> SSR_Selected True exact
            | Code_Identical \<Rightarrow> SSR_Selected False exact
            | Code_Replay_Conflict \<Rightarrow> SSR_Consume_Refused Conflicting_Wire_Replay)))"

fun ssr_checked where
  "ssr_checked (SSR_Selected first exact) = True"
| "ssr_checked _ = False"

fun ssr_fresh_binding where
  "ssr_fresh_binding (SSR_Selected first exact) = first"
| "ssr_fresh_binding _ = False"

fun ssr_binding_after where
  "ssr_binding_after (SSR_Selected True exact) prior = Some exact"
| "ssr_binding_after (SSR_Selected False exact) prior = prior"
| "ssr_binding_after _ prior = prior"

definition ssr_guard_replay where
  "ssr_guard_replay left right = length (filter ssr_checked [left,right])"

definition ssr_publish_one where
  "ssr_publish_one left right \<longleftrightarrow> ssr_fresh_binding left \<or> ssr_fresh_binding right"

text \<open>
  For this seed a fresh accepted label installs its exact UUID binding. The
  current read has no independent retained effect and the authorized exact ACK
  replay preserves its prior product image. Thus no new binding means no new
  image within this projection. The guard still replays each checked label,
  including the identical-arrival path. Counts refer to one journal candidate
  and its successful head selection, rather than backing-store method calls.
\<close>

lemma ssr_shape_failure_precedes_consume_and_keeps_binding:
  assumes "ssr_lane_shape lane = Some (Inl error)"
  shows "ssr_observe lane prior = SSR_Shape_Refused error"
    "\<not> ssr_checked (ssr_observe lane prior)"
    "ssr_binding_after (ssr_observe lane prior) prior = prior"
  using assms by (simp_all add: ssr_observe_def)

lemma ssr_valid_transport_operand_can_be_outside_scheduler_shape:
  assumes "code_check_declared_version raw limit = None"
    "decode_wire_packet raw = Some packet"
    "code_transport_operand_verdict (packet_core packet) 1 = Code_Operand_Accept"
    "\<not> ssr_in_schedule (packet_core packet)"
  shows "ssr_shape 6 limit True raw = Some (Inl Invalid_Wire_Format)"
  using assms by (simp add: ssr_shape_def)

lemma ssr_bad_ed25519_precedes_the_product_and_keeps_binding:
  assumes "ssr_lane_shape lane = Some (Inr packet)" "srl_credentials_match lane"
    "code_check_versioned_scope (packet_core packet) (srl_boundary lane) 6 = None"
    "wire_signature_scheme (packet_core packet) = 1" "\<not> srl_signature_valid lane"
  shows "ssr_observe lane prior = SSR_Consume_Refused Invalid_Wire_Signature"
    "\<not> ssr_checked (ssr_observe lane prior)"
    "ssr_binding_after (ssr_observe lane prior) prior = prior"
  using assms by (simp_all add: ssr_observe_def code_admit_packet_def Let_def)

lemma ssr_rejected_label_never_replays_and_the_survivor_controls_publication:
  "ssr_guard_replay (SSR_Shape_Refused error) survivor = (if ssr_checked survivor then 1 else 0)"
  "ssr_guard_replay survivor (SSR_Consume_Refused error) = (if ssr_checked survivor then 1 else 0)"
  "ssr_publish_one (SSR_Shape_Refused error) survivor = ssr_fresh_binding survivor"
  "ssr_publish_one survivor (SSR_Consume_Refused error) = ssr_fresh_binding survivor"
  by (simp_all add: ssr_guard_replay_def ssr_publish_one_def split: if_splits)

lemma ssr_exact_retry_revalidates_without_a_new_image:
  "ssr_guard_replay (SSR_Consume_Refused error) (SSR_Selected False exact) = 1"
  "\<not> ssr_publish_one (SSR_Consume_Refused error) (SSR_Selected False exact)"
  "ssr_binding_after (SSR_Selected False exact) (Some exact) = Some exact"
  by (simp_all add: ssr_guard_replay_def ssr_publish_one_def)

fun ssr_decode_lane :: "nat list list \<Rightarrow> ssr_lane option" where
  "ssr_decode_lane [[label,version,critical,configured,credential_match,signature_valid],
       values,families,atomicities,schemes,reference,raw] =
     (if length values = 13 \<and> max critical (max configured (max credential_match signature_valid)) \<le> 1 then
       Some \<lparr>srl_label = label,
         srl_boundary = code_contract_boundary values version families atomicities schemes (critical = 1),
         srl_nesting = values ! 12, srl_configured = (configured = 1),
         srl_credentials_match = (credential_match = 1), srl_signature_valid = (signature_valid = 1),
         srl_reference = reference, srl_raw = raw\<rparr> else None)"
| "ssr_decode_lane _ = None"

definition ssr_standalone_transport where
  "ssr_standalone_transport lane = fst (code_integer_reply
    (code_partial_transport_oracle (srl_raw lane) (srl_boundary lane) (srl_nesting lane)
      (srl_signature_valid lane) True None))"

fun ssr_label_words :: "nat \<Rightarrow> nat \<Rightarrow> ssr_result \<Rightarrow> nat list option" where
  "ssr_label_words role value (SSR_Shape_Refused error) =
    Some [0,code_transport_refusal_number error,0,0,0,0,0,0,0]"
| "ssr_label_words role value (SSR_Consume_Refused error) =
    Some [1,code_transport_refusal_number error,1,0,0,0,0,0,0]"
| "ssr_label_words role value SSR_Pending = None"
| "ssr_label_words role value (SSR_Selected first exact) =
    Some [2,(if first then 0 else 1),1,1,1,1,(if first then 1 else 0),role,value]"

definition ssr_batch_words where
  "ssr_batch_words proposed ack_label read_label ack_value read_value left right =
    (if proposed \<and> ssr_checked left \<and> ssr_checked right then None
     else Option.bind (ssr_label_words 1 ack_value left) (\<lambda>ack_words.
       Option.bind (ssr_label_words 2 read_value right) (\<lambda>read_words.
         let selected = (if ssr_publish_one left right then 1 else 0) in
         Some ([if proposed then 1 else 0,0,selected,selected,ssr_guard_replay left right,ack_label] @
           ack_words @ [read_label] @ read_words))))"

lemma ssr_left_refusal_preserves_original_labels_and_serializes:
  assumes "ssr_label_words 2 read_value right = Some read_words"
  shows "ssr_batch_words True ack_label read_label ack_value read_value
     (SSR_Shape_Refused error) right =
      Some ([1,0,(if ssr_fresh_binding right then 1 else 0),
        (if ssr_fresh_binding right then 1 else 0),(if ssr_checked right then 1 else 0),ack_label,
        0,code_transport_refusal_number error,0,0,0,0,0,0,0,read_label] @ read_words)"
  using assms by (cases "ssr_checked right"; simp add: ssr_batch_words_def ssr_guard_replay_def ssr_publish_one_def Let_def)

definition ssr_pair_integer ::
  "integer list \<Rightarrow> integer list list \<Rightarrow> integer list list \<Rightarrow> bool \<Rightarrow> integer list option" where
  "ssr_pair_integer seed left_words right_words proposed =
    (if \<not> list_all (\<lambda>word. 0 \<le> word) (seed @ concat left_words @ concat right_words) then None
     else Option.bind (ssr_decode_lane (map (map nat_of_integer) left_words)) (\<lambda>left.
       Option.bind (ssr_decode_lane (map (map nat_of_integer) right_words)) (\<lambda>right.
         case sw_compatible_pair_words (map nat_of_integer seed) (srl_reference left) (srl_reference right) of
           Some [ack_label,read_label,ack_value,_,_,_,_,_,read_value,_] \<Rightarrow>
             if ack_label \<noteq> srl_label left \<or> read_label \<noteq> srl_label right then None
             else let first_left = ssr_observe left None; first_right = ssr_observe right None;
                      retry_left = ssr_observe left (ssr_binding_after first_left None);
                      retry_right = ssr_observe right (ssr_binding_after first_right None)
                  in Option.bind (ssr_batch_words proposed ack_label read_label ack_value read_value first_left first_right)
                       (\<lambda>first. map_option (\<lambda>retry. ssr_standalone_transport left # ssr_standalone_transport right #
                          map integer_of_nat (first @ retry))
                         (ssr_batch_words proposed ack_label read_label ack_value read_value retry_left retry_right))
         | _ \<Rightarrow> None)))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ssr_shape_failure_precedes_consume_and_keeps_binding
      ssr_valid_transport_operand_can_be_outside_scheduler_shape
      ssr_bad_ed25519_precedes_the_product_and_keeps_binding
      ssr_rejected_label_never_replays_and_the_survivor_controls_publication
      ssr_exact_retry_revalidates_without_a_new_image ssr_left_refusal_preserves_original_labels_and_serializes})
  then () else error "Unexpected oracle in signed scheduler refusal claims"
\<close>

export_code ssr_pair_integer in SML module_name OIP_Signed_Schedule_Refusals
  file_prefix "oip_signed_schedule_refusals"

end
