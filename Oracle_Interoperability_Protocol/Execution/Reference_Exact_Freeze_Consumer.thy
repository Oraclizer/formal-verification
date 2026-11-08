theory Reference_Exact_Freeze_Consumer
  imports "OIP_Reference_Profile.Reference_Exact_Freeze_Packet" Reference_Runtime_Vectors
begin

definition decode_exact_ordinary_spend where
  "decode_exact_ordinary_spend bytes =
    (case decode_wire_packet bytes of None \<Rightarrow> None | Some packet \<Rightarrow>
      let core = packet_core packet; body = wire_operation_body core in
      if wire_message_family core \<noteq> Wire_State_Sync \<or> wire_opcode body \<noteq> 6 \<or> wire_deadline body \<noteq> Deadline_Absent then None
      else case decode_native_call_prefix core of None \<Rightarrow> None | Some native \<Rightarrow>
        (case (native_tail_words native,native_proof_bytes native) of ([position,sender,recipient,0],[raw]) \<Rightarrow>
          let amount = get_le_octets (rev raw) in
          if length raw = 32 \<and> wire_octets raw \<and> amount < 2^64 \<and>
             native_amount native < 2^64 \<and> wire_target_domain core = native_destination native
          then Some (native,position,sender,recipient,amount) else None | _ \<Rightarrow> None))"

definition spend_guard_observation where
  "spend_guard_observation check_mode exact_root bytes code =
    (case decode_exact_ordinary_spend bytes of None \<Rightarrow> None | Some (native,position,sender,recipient,amount) \<Rightarrow>
      let origin = native_origin native; domain = native_destination native; asset = native_asset native;
          source = (fst origin,asset); target = (domain,asset,recipient); lot = (origin,(domain,asset,sender));
          payer = rust_spend_source code source; received = rust_spend_destination code target;
          funded = rust_spend_funded code lot in
      if native_cut native \<noteq> rust_spend_cut code \<or> \<not> exact_root native position \<or> amount = 0 \<or> funded < amount \<or> payer < amount
      then None
      else if check_mode \<and> rust_spend_modes code (domain,asset) \<in> {None,Some FROZEN,Some SEIZED,Some CONFISCATED}
      then Some (False,payer,received,funded)
      else Some (True,payer - amount,received + amount,funded - amount))"

lemma the_same_frozen_spend_bytes_only_move_funds_when_the_policy_check_is_removed:
  "spend_guard_observation True (\<lambda>root position. native_origin root = (0,17) \<and> position = 5)
     guard_freeze_packet_bytes frozen_before = Some (False,5,0,5)"
  "spend_guard_observation False (\<lambda>root position. native_origin root = (0,17) \<and> position = 5)
     guard_freeze_packet_bytes frozen_before = Some (True,4,1,4)"
  by (simp_all add: spend_guard_observation_def decode_exact_ordinary_spend_def
      guard_freeze_decodes_from_the_full_native_envelope guard_freeze_core_def guard_freeze_body_def
      decode_native_call_prefix_def frozen_before_def wire_octets_def Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_same_frozen_spend_bytes_only_move_funds_when_the_policy_check_is_removed})
  then () else error "Unexpected oracle in exact frozen spend guard comparison"
\<close>

end
