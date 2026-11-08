theory Wire_Code_Resolution_Control
  imports Wire_Code_Fixed_Call_Request Wire_Code_Response_Outcome "OIP_Reference_Profile.Reference_Ordered_Control"
begin

record code_source_debit_request =
  source_debit_id :: client_call_id
  source_debit_origin :: source_key
  source_debit_generation :: nat
  source_debit_packet :: wire_bytes

definition code_source_debit_work :: "code_source_debit_request \<Rightarrow> (source_key \<times> nat)" where
  "code_source_debit_work request = (source_debit_origin request,source_debit_generation request)"

record code_source_control_observation =
  source_control_stored :: "nat \<times> wire_bytes"
  source_control_revoked :: "nat list"
  source_control_cancelled :: "authenticated_message_id list"
  source_control_decisions :: "(client_call_id \<times> (code_source_debit_request \<times> reference_disposition)) list"
  source_control_latest :: "((source_key \<times> nat) \<times> client_call_id) list"

definition code_source_resolution_principal_refusal :: "code_source_control_observation \<Rightarrow> nat \<Rightarrow> code_source_wire_error option" where
  "code_source_resolution_principal_refusal observed (actor_principal::nat) =
    (if actor_principal \<in> set (source_control_revoked observed)
     then Some (Code_Source_Wire_Validation Invalid_Wire_Source) else None)"

definition code_source_resolution_disposition :: "code_source_control_observation \<Rightarrow> code_source_debit_request \<Rightarrow> (code_source_wire_error + reference_disposition option)" where
  "code_source_resolution_disposition observed request =
    (case map_of (source_control_decisions observed) (source_debit_id request) of
       None \<Rightarrow> Inr None
     | Some (stored,status) \<Rightarrow>
         if stored = request then Inr (Some status)
         else Inl (Code_Source_Wire_Validation Conflicting_Wire_Replay))"

fun code_source_pending_transport_refusal ::
  "authenticated_message_id \<Rightarrow> wire_bytes \<Rightarrow>
    (client_call_id \<times> (code_source_debit_request \<times> reference_disposition)) list \<Rightarrow> code_source_wire_error option" where
  "code_source_pending_transport_refusal key packet [] = None"
| "code_source_pending_transport_refusal key packet ((call_id,(request,status)) # rest) =
    (if status \<noteq> Ref_Pending \<or> source_debit_packet request = packet
     then code_source_pending_transport_refusal key packet rest
     else case decode_wire_packet (source_debit_packet request) of
       None \<Rightarrow> Some (Code_Source_Wire_Recovery Code_Source_Recovery_Hold)
     | Some saved \<Rightarrow>
         if authenticated_wire_message_id (packet_core saved) = key
         then Some (Code_Source_Wire_Validation Conflicting_Wire_Replay)
         else code_source_pending_transport_refusal key packet rest)"

definition code_source_resolution_observation_fence :: "code_source_control_observation \<Rightarrow> (nat \<times> wire_bytes) option \<Rightarrow> code_source_wire_error option" where
  "code_source_resolution_observation_fence observed current_value =
    (case current_value of None \<Rightarrow> Some (Code_Source_Wire_Recovery Code_Source_Recovery_Hold)
     | Some actual \<Rightarrow> if actual = source_control_stored observed then None
       else Some (Code_Source_Wire_Recovery Code_Source_Recovery_Hold))"

datatype code_source_close_control_step =
    Code_Source_Close_Already_Rejected
  | Code_Source_Close_Replace
  | Code_Source_Close_Refused code_source_wire_error

definition code_source_reject_debit_step :: "code_source_control_observation \<Rightarrow> code_source_debit_request \<Rightarrow> code_source_close_control_step" where
  "code_source_reject_debit_step observed request =
    (case code_source_resolution_disposition observed request of
       Inl reason \<Rightarrow> Code_Source_Close_Refused reason
     | Inr status \<Rightarrow>
         if status = Some Ref_Explicit_Rejection then Code_Source_Close_Already_Rejected
         else if status = Some Ref_Pending \<or>
           (status = None \<and> map_of (source_control_latest observed) (code_source_debit_work request) = None)
         then Code_Source_Close_Replace
         else Code_Source_Close_Refused Code_Source_Wire_Unresolved)"

definition code_source_request_model_projection :: "code_source_debit_request \<Rightarrow> reference_original_debit option" where
  "code_source_request_model_projection request =
    map_option (\<lambda>packet.
      \<lparr>original_call = source_debit_id request,original_origin = source_debit_origin request,
       original_generation = source_debit_generation request,
       original_transport = authenticated_wire_message_id (packet_core packet),
       original_packet = source_debit_packet request\<rparr>) (decode_wire_packet (source_debit_packet request))"

lemma source_resolution_revocation_is_checked_but_cancellation_is_not_reconsumed:
  "code_source_resolution_principal_refusal observed actor_principal =
    code_source_resolution_principal_refusal (observed\<lparr>source_control_cancelled := cancelled\<rparr>) actor_principal"
  by (simp add: code_source_resolution_principal_refusal_def)

lemma a_changed_original_request_is_an_exact_disposition_conflict:
  assumes "map_of (source_control_decisions observed) (source_debit_id request) = Some (stored,status)"
    "stored \<noteq> request"
  shows "code_source_resolution_disposition observed request = Inl (Code_Source_Wire_Validation Conflicting_Wire_Replay)"
  using assms by (simp add: code_source_resolution_disposition_def)

lemma an_identical_pending_packet_needs_no_second_saved_packet_decode:
  "source_debit_packet request = packet \<Longrightarrow>
    code_source_pending_transport_refusal key packet ((call_id,(request,Ref_Pending)) # rest) =
      code_source_pending_transport_refusal key packet rest"
  by simp

lemma a_different_pending_body_for_the_same_authenticated_key_is_a_conflict:
  assumes "source_debit_packet request \<noteq> packet"
    "decode_wire_packet (source_debit_packet request) = Some saved"
    "authenticated_wire_message_id (packet_core saved) = key"
  shows "code_source_pending_transport_refusal key packet ((call_id,(request,Ref_Pending)) # rest) =
    Some (Code_Source_Wire_Validation Conflicting_Wire_Replay)"
  using assms by simp

theorem a_successful_resolution_fence_compares_the_actual_revision_and_exact_bytes:
  assumes "code_source_resolution_observation_fence observed current_value = None"
  shows "current_value = Some (source_control_stored observed)"
  using assms by (auto simp: code_source_resolution_observation_fence_def split: option.splits if_splits)

lemma a_changed_control_body_cannot_pass_even_with_the_same_physical_revision:
  assumes "source_control_stored observed = (revision,before)" "after \<noteq> before"
  shows "code_source_resolution_observation_fence observed (Some (revision,after)) =
    Some (Code_Source_Wire_Recovery Code_Source_Recovery_Hold)"
  using assms by (simp add: code_source_resolution_observation_fence_def)

lemma a_changed_physical_revision_cannot_pass_even_with_the_same_control_body:
  assumes "source_control_stored observed = (revision,bytes)" "later \<noteq> revision"
  shows "code_source_resolution_observation_fence observed (Some (later,bytes)) =
    Some (Code_Source_Wire_Recovery Code_Source_Recovery_Hold)"
  using assms by (simp add: code_source_resolution_observation_fence_def)

theorem the_source_original_request_transport_is_recomputed_from_its_own_packet:
  assumes "code_source_request_model_projection request = Some original"
  obtains packet :: wire_packet
  where "decode_wire_packet (source_debit_packet request) = Some packet"
    "original_transport original = authenticated_wire_message_id (packet_core packet)"
    "original_packet original = source_debit_packet request"
    "original_call original = source_debit_id request"
    "original_origin original = source_debit_origin request"
    "original_generation original = source_debit_generation request"
  using assms by (auto simp: code_source_request_model_projection_def split: option.splits)

text \<open>
  Source: ordered.rs OrderedCut authorize/disposition/check_pending_transport,
  unchanged and reject_debit's state decision before serialization/CAS.
  This observation is the selected already validated control: the full stored
  revision and bytes retain profile/head/writer and every field not inspected
  by these helpers. Its finite decision/latest rows must be the actual ordered
  BTreeMap projection, not an arbitrary replacement of those bytes.
  No physical revision is equated with the old logical Suc step counter.
  reject_debit serialization, exact replacement and caller return are linked
  by the resolver; Code_Source_Close_Replace alone is not a commit receipt.
\<close>

end
