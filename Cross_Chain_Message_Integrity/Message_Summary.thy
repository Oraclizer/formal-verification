(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Summary
  imports Message_Transport
begin

section \<open>A Checked Internal Summary\<close>

type_synonym checked_descriptor = "transfer_binding \<times> nat \<times> nat \<times> nat \<times> nat"

definition request_descriptor :: "execution_request \<Rightarrow> checked_descriptor" where
  "request_descriptor r = (request_binding r, certificate_epoch (request_certificate r),
    request_caller r, request_authority_epoch r, request_version r)"

definition descriptor_allowed :: "execution_context \<Rightarrow> checked_descriptor \<Rightarrow> bool"
  where
  "descriptor_allowed c d = (case d of (b,relay,caller,epoch,version) \<Rightarrow>
     binding_destination b = context_endpoint c \<and> relay = context_relay_epoch c \<and>
     epoch = context_authority_epoch c \<and> version = context_version c \<and>
     (caller,b) \<in> context_permissions c)"

definition summary_receive :: "execution_context \<Rightarrow> checked_descriptor option \<Rightarrow>
    message_state \<Rightarrow> message_state \<times> message_reply" where
  "summary_receive c summary s = (case summary of None \<Rightarrow> (s,Message_Rejected)
     | Some d \<Rightarrow> if \<not> descriptor_allowed c d then (s,Message_Rejected)
       else if credit_marker (fst d) \<in> consumed_at s then (s,Duplicate_Credit (fst d))
       else (record_credit (fst d) s,New_Credit (fst d)))"

definition separating_context :: "checked_descriptor \<Rightarrow> execution_context" where
  "separating_context d = (case d of (b,relay,caller,epoch,version) \<Rightarrow>
    \<lparr>context_endpoint = binding_destination b, context_relay_epoch = relay,
      context_authority_epoch = epoch, context_version = version,
      context_permissions = {(caller,b)}, context_readers = {}\<rparr>)"

lemma separating_context_allows_descriptor:
  "descriptor_allowed (separating_context d) d"
  by (cases d) (auto simp: descriptor_allowed_def separating_context_def split: prod.splits)

lemma separating_context_creates_credit:
  "summary_receive (separating_context d) (Some d) empty_message_state =
    (record_credit (fst d) empty_message_state,New_Credit (fst d))"
  by (simp add: summary_receive_def separating_context_allows_descriptor empty_message_state_def)

lemma separating_context_recovers_descriptor:
  assumes "descriptor_allowed (separating_context d) e"
  shows "d = e"
  using assms
  by (cases d; cases e)
     (auto simp: descriptor_allowed_def separating_context_def split: prod.splits)

theorem summary_observations_are_injective:
  assumes same: "\<forall>c s. summary_receive c left_summary s = summary_receive c right_summary s"
  shows "left_summary = right_summary"
proof (cases left_summary)
  case None
  show ?thesis
  proof (cases right_summary)
    case None
    then show ?thesis using \<open>left_summary = None\<close> by simp
  next
    case (Some d)
    have eq: "summary_receive (separating_context d) left_summary empty_message_state =
      summary_receive (separating_context d) right_summary empty_message_state"
      using same by blast
    have False using eq None Some separating_context_creates_credit[of d]
      by (simp add: summary_receive_def separating_context_allows_descriptor empty_message_state_def)
    then show ?thesis by blast
  qed
next
  case (Some d)
  note left = Some
  show ?thesis
  proof (cases right_summary)
    case None
    have eq: "summary_receive (separating_context d) left_summary empty_message_state =
      summary_receive (separating_context d) right_summary empty_message_state"
      using same by blast
    have False using eq left None separating_context_creates_credit[of d]
      by (simp add: summary_receive_def separating_context_allows_descriptor empty_message_state_def)
    then show ?thesis by blast
  next
    case (Some e)
    have eq: "summary_receive (separating_context d) (Some d) empty_message_state =
      summary_receive (separating_context d) (Some e) empty_message_state"
      using same left Some by blast
    have right_value: "summary_receive (separating_context d) (Some e) empty_message_state =
      (record_credit (fst d) empty_message_state, New_Credit (fst d))"
      by (rule trans[OF eq[symmetric] separating_context_creates_credit])
    have right_new: "snd (summary_receive (separating_context d) (Some e) empty_message_state) = New_Credit
      (fst d)"
      using arg_cong[OF right_value, where f=snd] by (simp only: snd_conv)
    have accepts: "descriptor_allowed (separating_context d) e"
      using right_new
      by (auto simp: summary_receive_def split: if_splits)
    have "d = e" using separating_context_recovers_descriptor[OF accepts] .
    then show ?thesis using left Some by simp
  qed
qed

context source_attestation
begin

definition intrinsic_credit_ok :: "execution_request \<Rightarrow> bool" where
  "intrinsic_credit_ok r \<longleftrightarrow>
     certificate_ok (request_certificate r) \<and>
     statement_binding (certificate_statement (request_certificate r)) = request_binding r \<and>
     statement_status (certificate_statement (request_certificate r)) = Finalized \<and>
     binding_operation (request_binding r) = Destination_Credit \<and>
     0 < binding_amount (request_binding r)"

definition checked_summary :: "normal_envelope \<Rightarrow> checked_descriptor option" where
  "checked_summary m = (if intrinsic_credit_ok (envelope_request m)
    then Some (request_descriptor (envelope_request m)) else None)"

lemma credit_admission_splits:
  "credit_admissible c r \<longleftrightarrow> intrinsic_credit_ok r \<and> descriptor_allowed c
    (request_descriptor r)"
  by (auto simp: credit_admissible_def intrinsic_credit_ok_def authenticated_request_def
      descriptor_allowed_def request_descriptor_def current_use_allowed_def)

theorem checked_summary_preserves_receiver:
  "summary_receive c (checked_summary m) s = receive_normal c m s"
  by (auto simp: summary_receive_def checked_summary_def request_descriptor_def receive_normal_def
      receive_credit_def credit_admission_splits split: if_splits)

theorem checked_summary_is_exact_information:
  "checked_summary m = checked_summary n \<longleftrightarrow>
    (\<forall>c s. receive_normal c m s = receive_normal c n s)"
proof
  assume same: "checked_summary m = checked_summary n"
  show "\<forall>c s. receive_normal c m s = receive_normal c n s"
    using checked_summary_preserves_receiver same by metis
next
  assume same: "\<forall>c s. receive_normal c m s = receive_normal c n s"
  have "\<forall>c s. summary_receive c (checked_summary m) s = summary_receive c (checked_summary n) s"
    using same checked_summary_preserves_receiver by metis
  then show "checked_summary m = checked_summary n" by (rule summary_observations_are_injective)
qed

end

definition refresh_descriptor :: "nat \<Rightarrow> nat \<Rightarrow> checked_descriptor \<Rightarrow>
  checked_descriptor" where
  "refresh_descriptor epoch version d = (case d of (b,relay,caller,old_epoch,old_version) \<Rightarrow>
    (b,relay,caller,epoch,version))"

context source_attestation
begin

theorem checked_summary_commutes_with_refresh:
  "checked_summary (refresh_envelope epoch version m) =
    map_option (refresh_descriptor epoch version) (checked_summary m)"
  by (simp add: checked_summary_def intrinsic_credit_ok_def request_descriptor_def
      refresh_descriptor_def refresh_envelope_def)

fun summary_trace :: "(execution_context \<times> checked_descriptor option) list \<Rightarrow>
    message_state \<Rightarrow> message_state \<times> message_reply list" where
  "summary_trace [] s = (s,[])"
| "summary_trace ((c,d)#xs) s =
    (let first = summary_receive c d s;
         rest = summary_trace xs (fst first)
     in (fst rest, snd first # snd rest))"

theorem checked_summary_preserves_finite_continuations:
  "summary_trace (map (\<lambda>(c,m). (c,checked_summary m)) xs) s = normal_trace xs s"
  by (induction xs arbitrary: s)
     (auto simp: Let_def checked_summary_preserves_receiver split: prod.splits)

end

text \<open>The summary is produced only after intrinsic verification. It is
  not a replacement wire certificate and must not be accepted as untrusted
  input. Exactness is relative to this receiver's full state and reply
  observations over all execution contexts in the model. It is not a theorem
  about all product-reachable policies or general continuation safety games.\<close>

end
