theory Wire_Debit_Bridge
  imports "Central_Product_Closure"
begin

definition signed_debit_request_matches where
  "signed_debit_request_matches native request \<longleftrightarrow>
    (let binding = request_binding request in
       binding_key binding = native_origin native \<and> binding_asset binding = native_asset native \<and>
       binding_amount binding = native_amount native \<and> binding_destination binding = native_destination native \<and>
       binding_recipient binding = native_recipient native \<and> request_caller request = fst (native_id native))"

definition debit_action_from_exact_operands where
  "debit_action_from_exact_operands route token endorsement core native credential versions generation request =
    (let caller = fst (native_id native); cut = native_cut native; target = wire_target_domain core;
         proof = \<lparr>proof_session = native_session native, proof_epoch = cut_authority_epoch cut\<rparr>;
         envelope = \<lparr>envelope_message = native_reference native, envelope_origin = native_origin native,
           envelope_asset = native_asset native, envelope_caller = caller, envelope_session = native_session native,
           envelope_cut = cut, envelope_command = Client_Protocol target 0 (Source_Intent request generation versions)\<rparr>;
         payload = \<lparr>payload_envelope = envelope, payload_credential = credential, payload_origin_epoch = native_origin_epoch native\<rparr>
     in Service_Execute route token proof target
       (Ordinary_Product_Action (Execute_Checked Normal_Lock_Entry caller cut (native_id native) payload)) endorsement)"

definition native_debit_header_allowed where
  "native_debit_header_allowed core native \<longleftrightarrow>
    native_amount native < 2^64 \<and> native_proof_bytes native = [] \<and>
    wire_deadline (wire_operation_body core) = Deadline_Absent \<and>
    wire_target_domain core = fst (native_origin native)"

definition select_wire_debit where
  "select_wire_debit route token endorsement attach core =
    (case decode_native_call_prefix core of None \<Rightarrow> None | Some native \<Rightarrow>
      if \<not> native_debit_header_allowed core native then None
      else case decode_ordinary_operands core native of
        Some (credential, versions, Wire_Debit generation) \<Rightarrow>
          (case attach native of None \<Rightarrow> None | Some request \<Rightarrow>
            if signed_debit_request_matches native request
            then Some (native_funding_owner native,
              debit_action_from_exact_operands route token endorsement core native credential versions generation request)
            else None)
      | _ \<Rightarrow> None)"

lemma selected_wire_debit_consumes_its_symbolic_amount_recipient_and_generation:
  assumes prefix: "decode_native_call_prefix core = Some native"
    and operands: "decode_ordinary_operands core native = Some (credential, versions, Wire_Debit generation)"
    and attached: "attach native = Some request"
    and selected: "select_wire_debit route token endorsement attach core = Some (owner, action)"
  shows "binding_amount (request_binding request) = native_amount native"
    "binding_recipient (request_binding request) = native_recipient native"
    "binding_key (request_binding request) = native_origin native"
    "owner = native_funding_owner native"
    "action = debit_action_from_exact_operands route token endorsement core native credential versions generation request"
    "native_debit_header_allowed core native"
  using selected
  by (simp_all add: select_wire_debit_def prefix operands attached signed_debit_request_matches_def Let_def split: if_splits)

lemma an_attachment_cannot_substitute_the_debit_amount_or_recipient:
  assumes prefix: "decode_native_call_prefix core = Some native"
    and operands: "decode_ordinary_operands core native = Some (credential, versions, Wire_Debit generation)"
    and attached: "attach native = Some request"
    and changed: "binding_amount (request_binding request) \<noteq> native_amount native \<or>
      binding_recipient (request_binding request) \<noteq> native_recipient native"
  shows "select_wire_debit route token endorsement attach core = None"
  using changed
  by (auto simp: select_wire_debit_def prefix operands attached signed_debit_request_matches_def Let_def)

context source_attestation
begin

lemma the_canonical_gate_alone_does_not_bind_the_selected_product_operands:
  assumes "wire_gate verify attest body_allowed scope bytes = Gate_Admitted packet"
  shows "service_action_from_wire verify attest body_allowed scope (\<lambda>_. Some substituted) bytes = Some substituted"
  using assms by (simp add: service_action_from_wire_def)

lemma actual_debit_selection_uses_the_received_signed_core:
  assumes "service_action_from_wire verify attest body_allowed scope
    (map_option snd \<circ> select_wire_debit route token endorsement attach) bytes = Some action"
  obtains packet native credential versions generation request owner where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes"
    "decode_native_call_prefix (packet_core packet) = Some native"
    "decode_ordinary_operands (packet_core packet) native = Some (credential, versions, Wire_Debit generation)"
    "attach native = Some request"
    "binding_amount (request_binding request) = native_amount native"
    "binding_recipient (request_binding request) = native_recipient native"
    "owner = native_funding_owner native"
    "action = debit_action_from_exact_operands route token endorsement (packet_core packet) native credential versions generation request"
proof -
  obtain packet where decoded: "decode_wire_packet bytes = Some packet"
    and encoded: "encode_wire_packet packet = bytes"
    and selected: "(map_option snd \<circ> select_wire_debit route token endorsement attach) (packet_core packet) = Some action"
    using admitted_canonical_bytes_are_the_only_input_to_the_selected_product_service[OF assms] by blast
  let ?core = "packet_core packet"
  obtain owner where chosen: "select_wire_debit route token endorsement attach ?core = Some (owner, action)"
    using selected by (cases "select_wire_debit route token endorsement attach ?core")
      (auto split: prod.splits)
  obtain native where prefix: "decode_native_call_prefix ?core = Some native"
    using chosen by (cases "decode_native_call_prefix ?core") (simp_all add: select_wire_debit_def)
  have representable: "native_debit_header_allowed ?core native"
  proof (rule ccontr)
    assume denied: "\<not> native_debit_header_allowed ?core native"
    with chosen prefix show False by (simp add: select_wire_debit_def)
  qed
  obtain credential versions generation where operands: "decode_ordinary_operands ?core native = Some (credential, versions, Wire_Debit generation)"
  proof (cases "decode_ordinary_operands ?core native")
    case None
    with chosen prefix representable show thesis by (simp add: select_wire_debit_def)
  next
    case (Some fields)
    obtain credential versions command where fields: "fields = (credential, versions, command)"
      by (cases fields) auto
    from Some fields chosen prefix representable show thesis
      by (cases command) (auto simp: select_wire_debit_def intro: that)
  qed
  obtain request where attached: "attach native = Some request"
    using chosen prefix operands representable by (cases "attach native") (simp_all add: select_wire_debit_def)
  note exact = selected_wire_debit_consumes_its_symbolic_amount_recipient_and_generation[OF prefix operands attached chosen]
  show thesis by (rule that[OF decoded encoded prefix operands attached exact(1,2,4,5)])
qed

thm_oracles selected_wire_debit_consumes_its_symbolic_amount_recipient_and_generation
  an_attachment_cannot_substitute_the_debit_amount_or_recipient
  actual_debit_selection_uses_the_received_signed_core

ML \<open>
  val _ =
    if null (Thm_Deps.all_oracles @{thms
      selected_wire_debit_consumes_its_symbolic_amount_recipient_and_generation
      an_attachment_cannot_substitute_the_debit_amount_or_recipient
      actual_debit_selection_uses_the_received_signed_core})
    then ()
    else error "The signed debit bridge depends on an oracle"
\<close>

end

end
