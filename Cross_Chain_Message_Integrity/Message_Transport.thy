(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Transport
  imports Message_Execution
begin

section \<open>Normal and Bypass Representations\<close>

record bypass_packet =
  bypass_certificate :: source_certificate
  bypass_caller :: nat
  bypass_authority_epoch :: nat
  bypass_version :: nat

definition decode_bypass :: "bypass_packet \<Rightarrow> execution_request" where
  "decode_bypass p =
    \<lparr>request_binding = statement_binding (certificate_statement (bypass_certificate p)),
      request_certificate = bypass_certificate p,
      request_caller = bypass_caller p,
      request_authority_epoch = bypass_authority_epoch p,
      request_version = bypass_version p\<rparr>"

definition encode_bypass :: "normal_envelope \<Rightarrow> bypass_packet option" where
  "encode_bypass m =
    (let r = envelope_request m in
     if request_binding r = statement_binding (certificate_statement (request_certificate r))
     then Some \<lparr>bypass_certificate = request_certificate r,
       bypass_caller = request_caller r,
       bypass_authority_epoch = request_authority_epoch r,
       bypass_version = request_version r\<rparr>
     else None)"

lemma decode_encoded_request:
  assumes "encode_bypass m = Some p"
  shows "decode_bypass p = envelope_request m"
  using assms
  unfolding encode_bypass_def decode_bypass_def Let_def
  by (cases "envelope_request m") (auto split: if_splits)

definition refresh_envelope :: "nat \<Rightarrow> nat \<Rightarrow> normal_envelope \<Rightarrow>
  normal_envelope" where
  "refresh_envelope epoch version m =
    m\<lparr>envelope_request := (envelope_request m)\<lparr>request_authority_epoch := epoch,
      request_version := version\<rparr>\<rparr>"

definition refresh_packet :: "nat \<Rightarrow> nat \<Rightarrow> bypass_packet \<Rightarrow> bypass_packet"
  where
  "refresh_packet epoch version p = p\<lparr>bypass_authority_epoch := epoch, bypass_version :=
    version\<rparr>"

theorem encoding_commutes_with_context_refresh:
  "encode_bypass (refresh_envelope epoch version m) =
    map_option (refresh_packet epoch version) (encode_bypass m)"
  by (simp add: encode_bypass_def refresh_envelope_def refresh_packet_def Let_def)

text \<open>Changing a claimed authority epoch or version does not grant a new
  permission. The receiver still compares it with the actual current context.
  Historical source and relay epochs are not changed by this translation.\<close>

context source_attestation
begin

definition receive_normal :: "execution_context \<Rightarrow> normal_envelope \<Rightarrow> message_state
  \<Rightarrow> message_state \<times> message_reply" where
  "receive_normal c m s = receive_credit Validated_Route c (envelope_request m) s"

definition receive_bypass :: "execution_context \<Rightarrow> bypass_packet option \<Rightarrow>
  message_state \<Rightarrow> message_state \<times> message_reply" where
  "receive_bypass c packet s =
     (case packet of None \<Rightarrow> (s, Message_Rejected)
      | Some p \<Rightarrow> receive_credit Bypass_Route c (decode_bypass p) s)"

lemma no_encoding_rejects_raw_request:
  assumes "encode_bypass m = None"
  shows "receive_normal c m s = (s, Message_Rejected)"
  using assms
  by (auto simp: encode_bypass_def Let_def receive_normal_def receive_credit_def
      credit_admissible_def authenticated_request_def split: if_splits)

theorem normal_bypass_guarantee_equivalence:
  "receive_bypass c (encode_bypass m) s = receive_normal c m s"
proof (cases "encode_bypass m")
  case None
  show ?thesis using no_encoding_rejects_raw_request[OF None]
    by (simp add: receive_bypass_def None)
next
  case (Some p)
  have decoded: "decode_bypass p = envelope_request m" using decode_encoded_request[OF Some] .
  show ?thesis
    by (simp add: receive_bypass_def receive_normal_def Some decoded receive_credit_def)
qed

fun normal_trace :: "(execution_context \<times> normal_envelope) list \<Rightarrow> message_state
  \<Rightarrow> message_state \<times> message_reply list" where
  "normal_trace [] s = (s, [])"
| "normal_trace ((c,m)#xs) s =
    (let first = receive_normal c m s;
         rest = normal_trace xs (fst first)
     in (fst rest, snd first # snd rest))"

fun bypass_trace :: "(execution_context \<times> bypass_packet option) list \<Rightarrow> message_state
  \<Rightarrow> message_state \<times> message_reply list" where
  "bypass_trace [] s = (s, [])"
| "bypass_trace ((c,p)#xs) s =
    (let first = receive_bypass c p s;
         rest = bypass_trace xs (fst first)
     in (fst rest, snd first # snd rest))"

theorem normal_bypass_finite_continuation_equivalence:
  "bypass_trace (map (\<lambda>(c,m). (c,encode_bypass m)) xs) s = normal_trace xs s"
  by (induction xs arbitrary: s)
     (auto simp: Let_def normal_bypass_guarantee_equivalence split: prod.splits)

definition normal_semantics :: "normal_envelope \<Rightarrow> (execution_context \<times> message_state)
  \<Rightarrow> message_state \<times> message_reply" where
  "normal_semantics m = (\<lambda>(c,s). receive_normal c m s)"

end

section \<open>Information Required by a Deterministic Translation\<close>

text \<open>The following factorization criterion is a standard information
  condition. It is applied to the actual receiver below, rather than assumed
  as a locale property. The concrete bypass decoder above is constructive;
  the choice in this existence proof is not an executable decoder.\<close>

theorem deterministic_factorization_iff:
  "(\<exists>decoder. \<forall>x. decoder (encoding x) = observation x) \<longleftrightarrow>
   (\<forall>x y. encoding x = encoding y \<longrightarrow> observation x = observation y)"
proof
  assume "\<exists>decoder. \<forall>x. decoder (encoding x) = observation x"
  then show "\<forall>x y. encoding x = encoding y \<longrightarrow> observation x = observation y" by metis
next
  assume fibres: "\<forall>x y. encoding x = encoding y \<longrightarrow> observation x = observation y"
  let ?decoder = "\<lambda>z. observation (SOME x. encoding x = z)"
  have pointwise: "\<forall>x. ?decoder (encoding x) = observation x"
  proof
    fix x
    have eq: "encoding (SOME y. encoding y = encoding x) = encoding x"
      by (rule someI[where P="\<lambda>y. encoding y = encoding x" and x=x]) simp
    show "?decoder (encoding x) = observation x" using fibres eq by blast
  qed
  show "\<exists>decoder. \<forall>x. decoder (encoding x) = observation x"
    by (rule exI[where x="?decoder"]) (rule pointwise)
qed

context source_attestation
begin

theorem route_information_sufficiency_iff:
  "(\<exists>receiver. \<forall>m. receiver (encoding m) = normal_semantics m) \<longleftrightarrow>
   (\<forall>m n. encoding m = encoding n \<longrightarrow>
     (\<forall>c s. receive_normal c m s = receive_normal c n s))"
  using deterministic_factorization_iff[of encoding normal_semantics]
  by (simp add: normal_semantics_def fun_eq_iff split_def)

theorem concrete_bypass_encoding_is_sufficient:
  "encode_bypass m = encode_bypass n \<Longrightarrow>
    receive_normal c m s = receive_normal c n s"
  using normal_bypass_guarantee_equivalence by metis

theorem separating_requests_prevent_exact_translation:
  assumes merged: "encoding m = encoding n"
    and separates: "receive_normal c m s \<noteq> receive_normal c n s"
  shows "\<not> (\<exists>receiver. \<forall>m. receiver (encoding m) = normal_semantics m)"
  using route_information_sufficiency_iff merged separates by blast

end

end
