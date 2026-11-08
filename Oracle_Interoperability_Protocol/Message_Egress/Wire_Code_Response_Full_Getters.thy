theory Wire_Code_Response_Full_Getters
  imports "OIP_Message_Response.Wire_Code_Response_Binding_Boundary"
    "OIP_Message_Response.Wire_Response_General_Receipt_Query"
begin

record code_response_full_context =
  full_response_config :: response_fixed_config
  full_response_channel :: response_fixed_channel
  full_response_site :: response_fixed_site
  full_parameters_clock :: "nat option"
  full_signing_clock :: "nat option"
  full_response_frame_limit :: nat

definition code_full_profile :: "nat list list \<Rightarrow> negotiated_wire_profile" where
  "code_full_profile = (\<lambda>oip_full_rows.
    \<lparr>negotiated_version = oip_full_rows ! 0 ! 0,
     negotiated_families = code_numeric_family_set (oip_full_rows ! 1),
     negotiated_atomicities = set (oip_full_rows ! 2),
     negotiated_schemes = set (oip_full_rows ! 3)\<rparr>)"

definition code_full_channel :: "nat list list \<Rightarrow> response_fixed_channel" where
  "code_full_channel = (\<lambda>oip_full_rows.
    \<lparr>response_channel_profile = code_full_profile oip_full_rows,
     response_channel_deployment = oip_full_rows ! 0 ! 1,
     response_channel_local = oip_full_rows ! 0 ! 2,
     response_channel_remote = oip_full_rows ! 0 ! 3,
     response_channel_expires = oip_full_rows ! 0 ! 4,
     response_channel_local_key = oip_full_rows ! 4,
     response_channel_remote_key = oip_full_rows ! 5\<rparr>)"

definition code_full_build_context ::
  "nat list list \<Rightarrow> nat option \<Rightarrow> nat option \<Rightarrow> code_response_full_context" where
  "code_full_build_context = (\<lambda>oip_full_rows oip_full_parameters_time oip_full_signing_time.
    \<lparr>full_response_config =
       \<lparr>response_config_deployment = oip_full_rows ! 6 ! 0,
        response_config_local_endpoints = set (oip_full_rows ! 7),
        response_config_peers = set (zip (oip_full_rows ! 8) (drop 14 oip_full_rows)),
        response_config_principal = oip_full_rows ! 6 ! 1,
        response_config_key = oip_full_rows ! 6 ! 2,
        response_config_epoch = oip_full_rows ! 6 ! 3,
        response_config_route = oip_full_rows ! 6 ! 4,
        response_config_ttl = oip_full_rows ! 6 ! 5,
        response_config_max_nesting = oip_full_rows ! 6 ! 6,
        response_config_public_key = oip_full_rows ! 9,
        response_config_policy_binding = oip_full_rows ! 10\<rparr>,
     full_response_channel = code_full_channel oip_full_rows,
     full_response_site =
       \<lparr>response_site_profile = (oip_full_rows ! 11 ! 0,oip_full_rows ! 11 ! 1,oip_full_rows ! 11 ! 2),
        response_site_ordered_control = (if oip_full_rows ! 11 ! 3 = 1 then Some () else None),
        response_site_security_ordered_profile =
          (if oip_full_rows ! 11 ! 4 = 1
           then Some (oip_full_rows ! 11 ! 5,oip_full_rows ! 11 ! 6,oip_full_rows ! 11 ! 7)
           else None)\<rparr>,
     full_parameters_clock = oip_full_parameters_time,
     full_signing_clock = oip_full_signing_time,
     full_response_frame_limit = oip_full_rows ! 13 ! 0\<rparr>)"

definition code_full_parse_context :: "nat list list \<Rightarrow> code_response_full_context option" where
  "code_full_parse_context = (\<lambda>oip_full_rows.
    if length oip_full_rows < 14 then None
    else if length (oip_full_rows ! 0) \<noteq> 5 \<or> length (oip_full_rows ! 6) \<noteq> 7 \<or>
      length (oip_full_rows ! 11) \<noteq> 8 \<or> length (oip_full_rows ! 12) \<noteq> 4 \<or>
      length (oip_full_rows ! 13) \<noteq> 1 \<or>
      length (oip_full_rows ! 8) \<noteq> length (drop 14 oip_full_rows) \<or>
      \<not> list_all (\<lambda>oip_full_key. length oip_full_key = 32)
        ([oip_full_rows ! 4,oip_full_rows ! 5,oip_full_rows ! 9,oip_full_rows ! 10] @ drop 14 oip_full_rows) \<or>
      oip_full_rows ! 11 ! 3 \<notin> {0,1} \<or> oip_full_rows ! 11 ! 4 \<notin> {0,1} \<or>
      \<not> list_all wire_octets
        ([oip_full_rows ! 4,oip_full_rows ! 5,oip_full_rows ! 9,oip_full_rows ! 10] @ drop 14 oip_full_rows)
    then None
    else Option.bind (code_rbound_position (oip_full_rows ! 12 ! 0) (oip_full_rows ! 12 ! 1))
      (\<lambda>oip_full_parameters_time.
        map_option (code_full_build_context oip_full_rows oip_full_parameters_time)
          (code_rbound_position (oip_full_rows ! 12 ! 2) (oip_full_rows ! 12 ! 3))))"

definition code_full_context_from_integer ::
  "integer list list \<Rightarrow> code_response_full_context option" where
  "code_full_context_from_integer = (\<lambda>oip_full_rows.
    if \<not> code_integer_u64_values (concat oip_full_rows) then None
    else code_full_parse_context (map (map nat_of_integer) oip_full_rows))"

definition code_full_build_client ::
  "nat list list \<Rightarrow> (response_fixed_channel \<times> response_fixed_client_boundary)" where
  "code_full_build_client = (\<lambda>oip_full_rows.
    (code_full_channel oip_full_rows,
      \<lparr>response_client_scope = code_contract_boundary (oip_full_rows ! 6)
        (oip_full_rows ! 0 ! 0) (oip_full_rows ! 1) (oip_full_rows ! 2) (oip_full_rows ! 3)
        (oip_full_rows ! 7 ! 0 = 1),
       response_client_public_key = oip_full_rows ! 8,
       response_client_max_nesting = oip_full_rows ! 6 ! 12\<rparr>))"

definition code_full_client_from_integer ::
  "integer list list \<Rightarrow> (response_fixed_channel \<times> response_fixed_client_boundary) option" where
  "code_full_client_from_integer = (\<lambda>oip_full_rows.
    if length oip_full_rows \<noteq> 9 \<or> \<not> code_integer_u64_values (concat oip_full_rows) then None
    else let oip_full_natural = map (map nat_of_integer) oip_full_rows in
      if length (oip_full_natural ! 0) \<noteq> 5 \<or> length (oip_full_natural ! 6) \<noteq> 13 \<or>
        length (oip_full_natural ! 7) \<noteq> 1 then None
      else if oip_full_natural ! 7 ! 0 \<notin> {0,1} \<or>
        \<not> list_all (\<lambda>oip_full_key. length oip_full_key = 32 \<and> wire_octets oip_full_key)
          [oip_full_natural ! 4,oip_full_natural ! 5,oip_full_natural ! 8] then None
      else Some (code_full_build_client oip_full_natural))"

lemma the_full_getters_preserve_every_peer_domain_and_key_pair:
  fixes oip_full_rows :: "nat list list"
    and oip_full_parameters_time oip_full_signing_time :: "nat option"
  shows "response_config_peers (full_response_config
      (code_full_build_context oip_full_rows oip_full_parameters_time oip_full_signing_time)) =
    set (zip (oip_full_rows ! 8) (drop 14 oip_full_rows))"
  by (simp add: code_full_build_context_def)

lemma the_full_getters_keep_local_identity_window_and_frame_limit:
  fixes oip_full_rows :: "nat list list"
    and oip_full_parameters_time oip_full_signing_time :: "nat option"
  shows "response_config_principal (full_response_config
      (code_full_build_context oip_full_rows oip_full_parameters_time oip_full_signing_time)) = oip_full_rows ! 6 ! 1"
    "response_config_key (full_response_config
      (code_full_build_context oip_full_rows oip_full_parameters_time oip_full_signing_time)) = oip_full_rows ! 6 ! 2"
    "response_channel_expires (full_response_channel
      (code_full_build_context oip_full_rows oip_full_parameters_time oip_full_signing_time)) = oip_full_rows ! 0 ! 4"
    "full_response_frame_limit
      (code_full_build_context oip_full_rows oip_full_parameters_time oip_full_signing_time) = oip_full_rows ! 13 ! 0"
  by (simp_all add: code_full_build_context_def code_full_channel_def)

lemma the_full_getters_do_not_identify_the_two_clock_reads:
  fixes oip_full_rows :: "nat list list"
    and oip_full_parameters_time oip_full_signing_time :: "nat option"
  shows "full_parameters_clock
      (code_full_build_context oip_full_rows oip_full_parameters_time oip_full_signing_time) = oip_full_parameters_time"
    "full_signing_clock
      (code_full_build_context oip_full_rows oip_full_parameters_time oip_full_signing_time) = oip_full_signing_time"
  by (simp_all add: code_full_build_context_def)

lemma the_full_getters_keep_the_actual_channel_atomicity_set:
  fixes oip_full_rows :: "nat list list"
  shows "negotiated_atomicities (response_channel_profile (code_full_channel oip_full_rows)) =
    set (oip_full_rows ! 2)"
  by (simp add: code_full_channel_def code_full_profile_def)

text \<open>
  These are finite value constructors from immutable provider/channel/site
  getters. A peer list is zipped with its keys; it is not collapsed into a
  map keyed by domain. Two peer principals at one domain may have two keys.
  Security-profile equality is computed from the actual optional triple.
  No current-channel success or whole-consumer Boolean is an ABI argument.
\<close>

end
