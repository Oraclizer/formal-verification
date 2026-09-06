(* SPDX-License-Identifier: BSD-3-Clause *)
theory Source_Certificates
  imports Message_Types
begin

section \<open>Threshold Authentication of Source Facts\<close>

text \<open>Cryptographic verification, honest attestation and stable source
  facts are separate assumptions. The checker uses the certificate and
  trusted epoch configuration. It does not query the source-truth predicate.\<close>

locale source_attestation =
  fixes roster :: "nat \<Rightarrow> nat set"
    and faulty :: "nat \<Rightarrow> nat set"
    and fault_bound :: "nat \<Rightarrow> nat"
    and threshold :: "nat \<Rightarrow> nat"
    and verifies :: "source_certificate \<Rightarrow> bool"
    and signed :: "nat \<Rightarrow> nat \<Rightarrow> source_statement \<Rightarrow> bool"
    and source_truth :: "source_statement \<Rightarrow> bool"
    and stable_source :: "source_key \<Rightarrow> source_statement option"
  assumes finite_roster: "finite (roster epoch)"
    and faulty_in_roster: "faulty epoch \<subseteq> roster epoch"
    and bounded_faults: "card (faulty epoch) \<le> fault_bound epoch"
    and honest_threshold: "fault_bound epoch < threshold epoch"
    and signature_sound:
      "\<lbrakk>verifies cert; signer \<in> set (certificate_signers cert)\<rbrakk> \<Longrightarrow>
       signed signer (certificate_epoch cert) (certificate_statement cert)"
    and honest_attests_truth:
      "\<lbrakk>signer \<in> roster epoch; signer \<notin> faulty epoch; signed signer epoch
        statement\<rbrakk>
       \<Longrightarrow> source_truth statement"
    and stable_fact_unique:
      "\<lbrakk>source_truth statement; statement_status statement \<noteq> Observed\<rbrakk>
       \<Longrightarrow> stable_source (binding_key (statement_binding statement)) = Some statement"
begin

definition certificate_ok :: "source_certificate \<Rightarrow> bool" where
  "certificate_ok cert \<longleftrightarrow>
     verifies cert \<and> distinct (certificate_signers cert) \<and>
     set (certificate_signers cert) \<subseteq> roster (certificate_epoch cert) \<and>
     threshold (certificate_epoch cert) \<le> length (certificate_signers cert)"

lemma finite_faulty: "finite (faulty epoch)"
  using finite_subset[OF faulty_in_roster finite_roster] .

lemma accepted_certificate_has_honest_signer:
  assumes accepted: "certificate_ok cert"
  shows "\<exists>signer \<in> set (certificate_signers cert).
    signer \<in> roster (certificate_epoch cert) \<and> signer \<notin> faulty (certificate_epoch cert)"
proof -
  have distinct: "distinct (certificate_signers cert)"
    and members: "set (certificate_signers cert) \<subseteq> roster (certificate_epoch cert)"
    and size: "threshold (certificate_epoch cert) \<le> length (certificate_signers cert)"
    using accepted unfolding certificate_ok_def by auto
  have card_signers: "card (set (certificate_signers cert)) = length (certificate_signers cert)"
    using distinct by (simp add: distinct_card)
  have not_faulty_only: "\<not> set (certificate_signers cert) \<subseteq> faulty (certificate_epoch cert)"
  proof
    assume subset: "set (certificate_signers cert) \<subseteq> faulty (certificate_epoch cert)"
    have "card (set (certificate_signers cert)) \<le> card (faulty (certificate_epoch cert))"
      using card_mono[OF finite_faulty subset] .
    with card_signers size bounded_faults[of "certificate_epoch cert"]
      honest_threshold[of "certificate_epoch cert"] show False by linarith
  qed
  with members show ?thesis by blast
qed

theorem certificate_authenticates_source_fact:
  assumes accepted: "certificate_ok cert"
  shows "source_truth (certificate_statement cert)"
proof -
  obtain signer where signer:
    "signer \<in> set (certificate_signers cert)"
    "signer \<in> roster (certificate_epoch cert)"
    "signer \<notin> faulty (certificate_epoch cert)"
    using accepted_certificate_has_honest_signer[OF accepted] by blast
  have verified: "verifies cert" using accepted unfolding certificate_ok_def by simp
  have attested: "signed signer (certificate_epoch cert) (certificate_statement cert)"
    using signature_sound[OF verified signer(1)] .
  show ?thesis using honest_attests_truth[OF signer(2,3) attested] .
qed

theorem certificate_authenticates_stable_fact:
  assumes "certificate_ok cert"
    and "statement_status (certificate_statement cert) \<noteq> Observed"
  shows "stable_source (binding_key (statement_binding (certificate_statement cert))) =
    Some (certificate_statement cert)"
  using stable_fact_unique[OF certificate_authenticates_source_fact[OF assms(1)] assms(2)] .

theorem stable_certificates_cannot_equivocate:
  assumes a: "certificate_ok a" and b: "certificate_ok b"
    and sa: "statement_status (certificate_statement a) \<noteq> Observed"
    and sb: "statement_status (certificate_statement b) \<noteq> Observed"
    and key: "binding_key (statement_binding (certificate_statement a)) =
      binding_key (statement_binding (certificate_statement b))"
  shows "certificate_statement a = certificate_statement b"
  using certificate_authenticates_stable_fact[OF a sa]
        certificate_authenticates_stable_fact[OF b sb] key by (metis option.inject)

definition authenticated_request :: "execution_context \<Rightarrow> execution_request \<Rightarrow> bool"
  where
  "authenticated_request c r \<longleftrightarrow>
     certificate_ok (request_certificate r) \<and>
     certificate_epoch (request_certificate r) = context_relay_epoch c \<and>
     statement_binding (certificate_statement (request_certificate r)) = request_binding r \<and>
     statement_status (certificate_statement (request_certificate r)) = Finalized \<and>
     binding_destination (request_binding r) = context_endpoint c \<and>
     current_use_allowed c r"

lemma request_has_stable_binding:
  assumes "authenticated_request c r"
  shows "stable_source (binding_key (request_binding r)) =
    Some \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
proof -
  have ok: "certificate_ok (request_certificate r)"
    and bound: "statement_binding (certificate_statement (request_certificate r)) = request_binding r"
    and status: "statement_status (certificate_statement (request_certificate r)) = Finalized"
    using assms unfolding authenticated_request_def by auto
  have whole: "certificate_statement (request_certificate r) =
    \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
    using bound status by (cases "certificate_statement (request_certificate r)") auto
  have stable: "stable_source (binding_key (statement_binding (certificate_statement (request_certificate
    r)))) =
      Some (certificate_statement (request_certificate r))"
    using certificate_authenticates_stable_fact[OF ok] status by simp
  show ?thesis using stable whole by simp
qed

theorem accepted_payload_is_bound:
  assumes "authenticated_request c r"
  shows "statement_binding (certificate_statement (request_certificate r)) = request_binding r \<and>
    request_authority_epoch r = context_authority_epoch c \<and>
    request_version r = context_version c \<and>
    (request_caller r, request_binding r) \<in> context_permissions c"
  using assms by (simp add: authenticated_request_def current_use_allowed_def)

end

end
