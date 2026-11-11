theory Refund_Source_Certificate_Link
  imports "OIP_Reference_Profile.Reference_Source_Reader_Code"
    "OIP_V062_Refund_Origin_Link.Refund_Origin_Link"
    "HOL-Library.Code_Target_Nat"
begin

type_synonym rsc_claim = "((nat \<times> nat) \<times> nat list, nat) reference_evidence_claim"

definition rsc_claim_at :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> rsc_claim" where
  "rsc_claim_at profile epoch domain event details =
    \<lparr>evidence_purpose = Source_Terminal, evidence_profile = profile,
      evidence_epoch = epoch, evidence_payload = ((domain, event), details)\<rparr>"

fun rsc_refund_claim :: "nat list \<Rightarrow> rsc_claim option" where
  "rsc_refund_claim [deployment, format, profile, epoch, domain, event,
       asset, owner, destination, recipient, amount, reference] =
    Some (rsc_claim_at profile epoch domain event
      [deployment, format, asset, owner, destination, recipient, amount, 2, reference])"
| "rsc_refund_claim _ = None"

fun rsc_certificate_claim :: "nat list \<Rightarrow> rsc_claim option" where
  "rsc_certificate_claim [deployment, format, profile, epoch, domain, event,
       asset, owner, destination, recipient, amount, kind, reference] =
    (if kind = 1 \<or> kind = 2 then Some (rsc_claim_at profile epoch domain event
      [deployment, format, asset, owner, destination, recipient, amount, kind, reference]) else None)"
| "rsc_certificate_claim _ = None"

definition rsc_proof_code ::
  "nat \<Rightarrow> rsc_claim \<Rightarrow> rsc_claim \<Rightarrow>
   (evidence_purpose \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list option) \<Rightarrow>
   (nat list \<Rightarrow> rsc_claim \<Rightarrow> nat list \<Rightarrow> bool) \<Rightarrow>
   nat \<Rightarrow> (nat \<times> nat list) list \<Rightarrow> nat" where
  "rsc_proof_code proof_count expected supplied keys verify required votes =
    (if proof_count \<noteq> 1 then 3
     else if expected \<noteq> supplied then 1
     else if source_certificate_quorum keys verify required expected votes then 0
     else 2)"

lemma rsc_mismatched_statement_precedes_quorum:
  assumes "expected \<noteq> supplied"
  shows "rsc_proof_code 1 expected supplied keys verify required votes = 1"
  using assms by (simp add: rsc_proof_code_def)

lemma rsc_reference_is_an_exact_statement_field:
  assumes "requested \<noteq> selected"
  shows "rsc_proof_code 1
    (rsc_claim_at profile epoch domain event (fixed @ [requested]))
    (rsc_claim_at profile epoch domain event (fixed @ [selected]))
    keys verify required votes = 1"
  using assms by (simp add: rsc_proof_code_def rsc_claim_at_def)

lemma rsc_success_supplies_exact_claim_and_quorum:
  assumes "rsc_proof_code proof_count expected supplied keys verify required votes = 0"
  shows "proof_count = 1" "expected = supplied"
    "source_certificate_quorum keys verify required expected votes"
  using assms by (auto simp: rsc_proof_code_def split: if_splits)

theorem rsc_accepted_quorum_from_selected_reader:
  assumes pass: "rsc_proof_code proof_count claim supplied keys verify required votes = 0"
    and read: "read_rust_source_decision decode encode hash registered valid revision bytes witness
      (evidence_profile claim, fst (evidence_payload claim)) =
        Some (evidence_epoch claim, snd (evidence_payload claim))"
    and related: "rust_selected_source_view witness = source_selected_observation model"
  shows "authoritative_source_certificate (source_selection model) keys verify required claim votes"
  by (rule the_rust_read_before_quorum_signing_supplies_the_authoritative_certificate_record
    [OF read related rsc_success_supplies_exact_claim_and_quorum(3)[OF pass]])

lemmas rsc_downstream_reference_guard =
  source_attestation.ror_missing_exact_reference_leaves_financial_state

definition rsc_keys ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat list) list \<Rightarrow> rsc_claim \<Rightarrow>
   evidence_purpose \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list option" where
  "rsc_keys rsc_rule_domain rsc_rule_epoch rsc_registry rsc_supplied rsc_purpose rsc_epoch rsc_signer =
    (if rsc_rule_domain = fst (fst (evidence_payload rsc_supplied)) \<and>
        rsc_purpose = Source_Terminal \<and> rsc_epoch = rsc_rule_epoch
     then map_of rsc_registry rsc_signer else None)"

definition rsc_octets :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "rsc_octets rsc_width rsc_bytes \<longleftrightarrow>
    length rsc_bytes = rsc_width \<and> list_all (\<lambda>rsc_octet. rsc_octet < 256) rsc_bytes"

fun rsc_run :: "nat list list \<Rightarrow> nat list option" where
  "rsc_run [rsc_request, rsc_certificate, [rsc_count, rsc_domain, rsc_epoch, rsc_quorum],
      rsc_signer1 # rsc_key1, rsc_signer2 # rsc_key2, rsc_vote1 # rsc_signature1,
      rsc_vote2 # rsc_signature2, [rsc_verified1, rsc_verified2]] =
    (if rsc_octets 32 rsc_key1 \<and> rsc_octets 32 rsc_key2 \<and>
        rsc_octets 64 rsc_signature1 \<and> rsc_octets 64 rsc_signature2 \<and>
        rsc_verified1 \<le> 1 \<and> rsc_verified2 \<le> 1
     then
       (case (rsc_refund_claim rsc_request, rsc_certificate_claim rsc_certificate) of
         (Some rsc_expected, Some rsc_supplied) \<Rightarrow>
           (let rsc_key_at = rsc_keys rsc_domain rsc_epoch
                  [(rsc_signer1, rsc_key1), (rsc_signer2, rsc_key2)] rsc_supplied;
                rsc_verified = (\<lambda>rsc_key rsc_claim_arg rsc_signature. rsc_claim_arg = rsc_supplied \<and>
                  ((rsc_verified1 = 1 \<and> rsc_key = rsc_key1 \<and> rsc_signature = rsc_signature1) \<or>
                   (rsc_verified2 = 1 \<and> rsc_key = rsc_key2 \<and> rsc_signature = rsc_signature2)));
                rsc_result = rsc_proof_code rsc_count rsc_expected rsc_supplied rsc_key_at rsc_verified rsc_quorum
                  [(rsc_vote1, rsc_signature1), (rsc_vote2, rsc_signature2)]
            in Some [rsc_result, last rsc_request, last rsc_certificate])
       | _ \<Rightarrow> None)
     else None)"
| "rsc_run _ = None"

definition rsc_submit_integer :: "integer list list \<Rightarrow> integer list option" where
  "rsc_submit_integer rsc_rows =
    (if list_all (list_all (\<lambda>rsc_word. 0 \<le> rsc_word)) rsc_rows
     then map_option (map integer_of_nat) (rsc_run (map (map nat_of_integer) rsc_rows))
     else None)"

declare registered_reference_proof_def [code del]
declare source_certificate_quorum_def [code del]

lemma rsc_registered_reference_proof_code [code]:
  "registered_reference_proof rsc_lookup rsc_verify rsc_item rsc_signer rsc_signature =
    (case rsc_lookup (evidence_purpose rsc_item) (evidence_epoch rsc_item) rsc_signer of
       None \<Rightarrow> False | Some rsc_key \<Rightarrow> rsc_verify rsc_key rsc_item rsc_signature)"
  by (cases "rsc_lookup (evidence_purpose rsc_item) (evidence_epoch rsc_item) rsc_signer")
     (simp_all add: registered_reference_proof_def)

lemma rsc_source_certificate_quorum_code [code]:
  "source_certificate_quorum rsc_lookup rsc_verify rsc_required rsc_item rsc_votes =
    (evidence_purpose rsc_item = Source_Terminal \<and>
     0 < rsc_required \<and> rsc_required \<le> length rsc_votes \<and>
     distinct (map fst rsc_votes) \<and>
     distinct (map (\<lambda>(rsc_signer, _). rsc_lookup Source_Terminal (evidence_epoch rsc_item) rsc_signer) rsc_votes) \<and>
     list_all (\<lambda>(rsc_signer, rsc_signature).
       registered_reference_proof rsc_lookup rsc_verify rsc_item rsc_signer rsc_signature) rsc_votes)"
  by (simp add: source_certificate_quorum_def list_all_iff)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms rsc_mismatched_statement_precedes_quorum
      rsc_reference_is_an_exact_statement_field rsc_success_supplies_exact_claim_and_quorum
      rsc_accepted_quorum_from_selected_reader rsc_downstream_reference_guard
      rsc_registered_reference_proof_code rsc_source_certificate_quorum_code})
  then () else error "Unexpected oracle in Refund source certificate link"
\<close>

export_code rsc_submit_integer in SML module_name OIP_Refund_Source_Certificate_ABI
  file_prefix oip_refund_source_certificate

end
