theory Wire_Negotiation
  imports Wire_Packet
begin

record peer_offer =
  offer_deployment :: nat
  offer_sender :: nat
  offer_receiver :: nat
  offer_challenge :: nat
  offer_expires :: nat
  offered_versions :: "nat set"
  offered_families :: "wire_family set"
  offered_atomicities :: "nat set"
  offered_schemes :: "nat set"

record negotiated_wire_profile =
  negotiated_version :: nat
  negotiated_families :: "wire_family set"
  negotiated_atomicities :: "nat set"
  negotiated_schemes :: "nat set"

definition selected_wire_version :: "nat \<Rightarrow> nat set \<Rightarrow> nat option" where
  "selected_wire_version floor common =
    (if floor \<le> 6 \<and> 6 \<in> common then Some 6
     else if floor \<le> 5 \<and> 5 \<in> common then Some 5 else None)"

definition authenticated_wire_negotiation where
  "authenticated_wire_negotiation verify confirm deployment sender receiver challenge floor now local remote =
    (if offer_deployment local = deployment \<and> offer_deployment remote = deployment \<and>
       offer_sender local = sender \<and> offer_receiver local = receiver \<and>
       offer_sender remote = receiver \<and> offer_receiver remote = sender \<and>
       offer_challenge local = challenge \<and> offer_challenge remote = challenge \<and>
       now \<le> offer_expires local \<and> now \<le> offer_expires remote \<and> verify local \<and> verify remote
     then case selected_wire_version floor (offered_versions local \<inter> offered_versions remote) of None \<Rightarrow> None
       | Some version \<Rightarrow> let profile = \<lparr>negotiated_version = version,
           negotiated_families = offered_families local \<inter> offered_families remote,
           negotiated_atomicities = offered_atomicities local \<inter> offered_atomicities remote,
           negotiated_schemes = offered_schemes local \<inter> offered_schemes remote\<rparr>
         in if confirm local remote profile then Some profile else None
     else None)"

lemma authenticated_highest_common_version_cannot_downgrade:
  assumes "authenticated_wire_negotiation verify confirm deployment sender receiver challenge floor now local remote = Some profile"
    "6 \<in> offered_versions local" "6 \<in> offered_versions remote" "floor \<le> 6"
  shows "negotiated_version profile = 6"
  using assms by (auto simp: authenticated_wire_negotiation_def selected_wire_version_def Let_def split: if_splits)

lemma an_unverified_offer_never_selects_a_legacy_or_current_profile:
  assumes "\<not> verify remote"
  shows "authenticated_wire_negotiation verify confirm deployment sender receiver challenge floor now local remote = None"
  using assms by (simp add: authenticated_wire_negotiation_def)

lemma stale_challenge_or_expiry_prevents_selection:
  assumes "offer_challenge remote \<noteq> challenge \<or> offer_expires remote < now"
  shows "authenticated_wire_negotiation verify confirm deployment sender receiver challenge floor now local remote = None"
  using assms by (auto simp: authenticated_wire_negotiation_def)

datatype 'message versioned_ingress = Decoded_Legacy 'message | Decoded_Canonical wire_packet

definition decode_for_negotiated_version where
  "decode_for_negotiated_version legacy_decode profile bytes =
    (if negotiated_version profile = 5 then map_option Decoded_Legacy (legacy_decode bytes)
     else if negotiated_version profile = 6 then map_option Decoded_Canonical (decode_wire_packet bytes)
     else None)"

lemma canonical_parse_failure_never_calls_the_legacy_decoder:
  assumes "negotiated_version profile = 6" "decode_wire_packet bytes = None"
  shows "decode_for_negotiated_version legacy_decode profile bytes = None"
  using assms by (simp add: decode_for_negotiated_version_def)

lemma legacy_profile_uses_only_the_explicit_compatibility_adapter:
  assumes "negotiated_version profile = 5" "legacy_decode bytes = Some message"
  shows "decode_for_negotiated_version legacy_decode profile bytes = Some (Decoded_Legacy message)"
  using assms by (simp add: decode_for_negotiated_version_def)

end
