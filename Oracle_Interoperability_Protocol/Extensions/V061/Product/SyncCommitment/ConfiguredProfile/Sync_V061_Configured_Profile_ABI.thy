theory Sync_V061_Configured_Profile_ABI
  imports "OIP_Sync_V061_Wire_V4.Sync_V061_Wire"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen"
begin

type_synonym sync_profile_view = "nat list \<times> wire_bytes list"

definition sync_profile_operations where
  "sync_profile_operations pairs = set (concat (map (\<lambda>(number,opcode).
    case family_at_number number of None \<Rightarrow> [] | Some family \<Rightarrow> [(family,opcode)]) pairs))"

definition sync_profile_view :: "bool \<Rightarrow> wire_gate_result \<Rightarrow> sync_profile_view" where
  "sync_profile_view canonical gate =
    (let consume = (\<lambda>_ (calls,bindings). ((Suc calls,Suc bindings),()));
         ((calls,bindings),result) = sync_route_gate consume gate (0,0);
         code = (case result of Inl reason \<Rightarrow> code_transport_refusal_number reason | Inr _ \<Rightarrow> 0)
     in ([if canonical then 1 else 0,code,calls,bindings],[]))"

lemma sync_profile_refusal_view:
  "sync_profile_view canonical (Gate_Refused reason) =
    ([if canonical then 1 else 0,code_transport_refusal_number reason,0,0],[])"
  by (simp add: sync_profile_view_def Let_def)

definition sync_profile_run where
  "sync_profile_run row_specification row_boundary row_public_key row_fact row_operations row_raw =
    (let verify = (\<lambda>_ row_message row_signature. row_fact = (row_public_key,row_message,row_signature,True));
         gate = sync_v6_gate row_specification (sync_profile_operations row_operations) verify (\<lambda>_. False)
           (\<lambda>_ _. True) row_boundary row_raw
     in sync_profile_view (sync_packet_for row_specification row_raw \<noteq> None) gate)"

definition sync_profile_case where
  "sync_profile_case row_profile row_input =
    (case row_input of (row_raw,row_config,row_operations,row_control,row_public_key,row_fact) \<Rightarrow>
      (case row_config of [cfg_old,cfg_deployment,cfg_source,cfg_target,cfg_principal,cfg_key,cfg_epoch,cfg_route,
        cfg_now,cfg_ttl,cfg_skew,cfg_frame,cfg_floor,cfg_critical] \<Rightarrow>
        let row_specification = (if cfg_old = 1 then Sync_V060 else Sync_V061);
            row_boundary = \<lparr>boundary_profile = row_profile, boundary_deployment = cfg_deployment,
              boundary_source = cfg_source, boundary_target = cfg_target, boundary_principal = cfg_principal,
              boundary_key = cfg_key, boundary_epoch = cfg_epoch, boundary_route_scope = cfg_route,
              boundary_now = cfg_now, boundary_asset_ttl_floor = cfg_ttl, boundary_future_skew = cfg_skew,
              boundary_max_frame = cfg_frame, boundary_version_floor = cfg_floor,
              boundary_critical_allowed = (cfg_critical = 1), boundary_threshold_supported = False\<rparr>;
            run = (\<lambda>row_choices. sync_profile_run row_specification row_boundary row_public_key row_fact row_choices row_raw)
        in (run row_operations,case row_control of None \<Rightarrow> ([],[]) | Some row_enabled \<Rightarrow> run row_enabled)
      | _ \<Rightarrow> (([],[]),([],[]))))"

definition sync_configured_profile_integer_trace where
  "sync_configured_profile_integer_trace input_version input_families input_atomicities input_schemes input_rows =
    (let n = nat_of_integer; ns = map n;
         numeric_pair = (\<lambda>(family,opcode). (n family,n opcode));
         output = (\<lambda>(words,blobs). (map integer_of_nat words,map (map integer_of_nat) blobs));
         row_profile = \<lparr>negotiated_version = n input_version, negotiated_families = code_numeric_family_set (ns input_families),
           negotiated_atomicities = set (ns input_atomicities), negotiated_schemes = set (ns input_schemes)\<rparr>;
         steps = map (\<lambda>(row_raw,row_cfg,row_operations,row_control,row_key,(row_fact_key,row_message,row_signature,row_verified)).
           (ns row_raw,ns row_cfg,map numeric_pair row_operations,map_option (map numeric_pair) row_control,ns row_key,
             (ns row_fact_key,ns row_message,ns row_signature,(row_verified :: integer) = 1))) input_rows
     in Some (map (\<lambda>row_input. case sync_profile_case row_profile row_input of (row_primary,row_control) \<Rightarrow>
          (output row_primary,output row_control)) steps))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_profile_refusal_view})
  then () else error "Unexpected oracle in the configured profile observation"
\<close>

export_code sync_configured_profile_integer_trace
  in SML module_name OIP_Sync_Configured_Profile_ABI file_prefix "oip_sync_configured_profile_abi"

end
