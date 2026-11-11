theory Query6_Capture_G0
  imports "OIP_Message_Code.Wire_Code_Read_Service"
begin

text \<open>
  A separate capture authorization boundary. Verified identity and exact signed
  capture intent are explicit facts supplied by an external authenticator.
  There is no constant-True signature verifier. This theory neither establishes
  cryptographic truth nor runs the old Current_Data capture policy in its place.
  The product read is pure; transport binding publication is outside this slice.
\<close>

record query6_capture_scope =
  q6_scope_principal :: nat
  q6_scope_proof :: session_proof
  q6_scope_target :: nat
  q6_scope_query :: application_query

record query6_auth_facts =
  q6_authenticated_subject :: "(nat \<times> nat) option"
  q6_active_proof :: "session_proof option"
  q6_verified_capture :: "query6_capture_scope option"
  q6_registered_targets :: "nat list"
  q6_current_epoch :: nat
  q6_authority_available :: bool
  q6_cache_grants :: "query6_capture_scope list"
  q6_current_grants :: "query6_capture_scope list"

datatype query6_capture_reply =
    Q6_Not_Capture
  | Q6_Endpoint_Rejected
  | Q6_Endpoint_Unavailable
  | Q6_Cache_Error product_read_reply
  | Q6_Cache_Value product_cache_entry

definition query6_capture_permission where
  "query6_capture_permission permit_current_fallback requested facts \<longleftrightarrow>
    requested \<in> set (q6_cache_grants facts) \<or>
    (permit_current_fallback \<and> requested \<in> set (q6_current_grants facts))"

definition query6_current_permission where
  "query6_current_permission requested facts \<longleftrightarrow>
    requested \<in> set (q6_current_grants facts)"

definition query6_auth_matches where
  "query6_auth_matches token requested facts \<longleftrightarrow>
    q6_authenticated_subject facts = Some (token, q6_scope_principal requested) \<and>
    q6_active_proof facts = Some (q6_scope_proof requested) \<and>
    proof_epoch (q6_scope_proof requested) = q6_current_epoch facts \<and>
    q6_scope_target requested \<in> set (q6_registered_targets facts) \<and>
    q6_verified_capture facts = Some requested"

fun query6_capture_from_current :: "nat \<Rightarrow> application_query \<Rightarrow> product_read_reply \<Rightarrow> query6_capture_reply" where
  "query6_capture_from_current provider query (Current_Cut_Value selected_cut observed_value) =
    Q6_Cache_Value \<lparr>cached_query = query, cached_provider = provider,
      cached_cut = selected_cut, cached_value = observed_value\<rparr>"
| "query6_capture_from_current provider query upstream = Q6_Cache_Error upstream"

definition query6_capture_boundary where
  "query6_capture_boundary permit_current_fallback token requested facts provider upstream product_state =
    (product_state,
      if \<not> query6_auth_matches token requested facts \<or>
         \<not> query6_capture_permission permit_current_fallback requested facts
      then Q6_Endpoint_Rejected
      else if \<not> q6_authority_available facts then Q6_Endpoint_Unavailable
      else query6_capture_from_current provider (q6_scope_query requested) upstream)"

definition query6_capture_from_core where
  "query6_capture_from_core permit_current_fallback token core facts provider upstream product_state =
    (case code_source_nonreceipt_read_service token core of
      Some (Service_Capture selected_token selected_proof selected_target selected_query) \<Rightarrow>
        query6_capture_boundary permit_current_fallback selected_token
          \<lparr>q6_scope_principal = wire_principal core, q6_scope_proof = selected_proof,
           q6_scope_target = selected_target, q6_scope_query = selected_query\<rparr>
          facts provider upstream product_state
    | _ \<Rightarrow> (product_state, Q6_Not_Capture))"

lemma query6_exact_capture_selector_is_reused:
  assumes "wire_message_family core = Wire_Query"
    "wire_opcode (wire_operation_body core) = 6"
    "wire_words (wire_operation_body core) = [selected_session,1,selected_asset]"
    "wire_blobs (wire_operation_body core) = []"
    "wire_deadline (wire_operation_body core) = Deadline_Absent"
  shows "code_source_nonreceipt_read_service token core = Some
    (Service_Capture token \<lparr>proof_session = selected_session,
      proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) (Application_Value selected_asset))"
  using assms by (simp add: code_source_nonreceipt_read_service_def code_decode_query_nonreceipt_def
      decode_wire_query_body_def parse_wire_application_query_def Let_def)

lemma query6_capture_is_product_pure:
  "fst (query6_capture_boundary fallback token requested facts provider upstream product_state) = product_state"
  by (simp add: query6_capture_boundary_def)

lemma query6_success_uses_capture_grant_and_exact_scope:
  assumes "snd (query6_capture_boundary False token requested facts provider upstream product_state) = Q6_Cache_Value entry"
  shows "query6_auth_matches token requested facts"
    "requested \<in> set (q6_cache_grants facts)"
    "q6_authority_available facts"
    "cached_provider entry = provider"
    "cached_query entry = q6_scope_query requested"
    "upstream = Current_Cut_Value (cached_cut entry) (cached_value entry)"
  using assms
  by (cases upstream; auto simp: query6_capture_boundary_def query6_capture_permission_def split: if_splits)+

lemma query6_current_grant_alone_cannot_capture:
  assumes "requested \<notin> set (q6_cache_grants facts)"
  shows "query6_capture_boundary False token requested facts provider upstream product_state =
    (product_state, Q6_Endpoint_Rejected)"
  using assms by (simp add: query6_capture_boundary_def query6_capture_permission_def)

lemma query6_endpoint_failure_and_cache_failure_are_distinct:
  "Q6_Endpoint_Rejected \<noteq> Q6_Cache_Error Product_Read_Rejected"
  "Q6_Endpoint_Unavailable \<noteq> Q6_Cache_Error Product_Read_Unavailable"
  by simp_all

definition query6_g0_core :: wire_core where
  "query6_g0_core = \<lparr>wire_version = 6, wire_purpose = 1, wire_deployment = 7,
    wire_source_domain = 0, wire_target_domain = 2, wire_principal = 7,
    wire_key_number = 9, wire_authority_epoch = 9, wire_sent_seconds = 100,
    wire_ttl_seconds = 5, wire_uuid = [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_Query, wire_primary_code = 1, wire_secondary_code = Some 77,
    wire_signature_scheme = 1,
    wire_operation_body = \<lparr>wire_opcode = 6, wire_words = [2,1,17],
      wire_blobs = [], wire_deadline = Deadline_Absent\<rparr>,
    wire_atomicity = 3, wire_priority = 3, wire_route_scope = 1\<rparr>"

definition query6_g0_scope :: query6_capture_scope where
  "query6_g0_scope = \<lparr>q6_scope_principal = 7,
    q6_scope_proof = \<lparr>proof_session = 2, proof_epoch = 9\<rparr>,
    q6_scope_target = 2, q6_scope_query = Application_Value 17\<rparr>"

definition query6_g0_facts where
  "query6_g0_facts cache_assets current_assets =
    \<lparr>q6_authenticated_subject = Some (7,7),
     q6_active_proof = Some \<lparr>proof_session = 2, proof_epoch = 9\<rparr>,
     q6_verified_capture = Some query6_g0_scope, q6_registered_targets = [2],
     q6_current_epoch = 9, q6_authority_available = True,
     q6_cache_grants = map (\<lambda>asset. query6_g0_scope\<lparr>q6_scope_query := Application_Value asset\<rparr>) cache_assets,
     q6_current_grants = map (\<lambda>asset. query6_g0_scope\<lparr>q6_scope_query := Application_Value asset\<rparr>) current_assets\<rparr>"

definition query6_g0_cut :: product_cut where
  "query6_g0_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 0\<rparr>"

definition query6_g0_entry :: product_cache_entry where
  "query6_g0_entry = \<lparr>cached_query = Application_Value 17, cached_provider = 100,
    cached_cut = query6_g0_cut, cached_value = Units_Value 0\<rparr>"

lemma query6_g0_selected_service:
  "code_source_nonreceipt_read_service (7::nat) query6_g0_core =
    Some (Service_Capture 7 \<lparr>proof_session = 2, proof_epoch = 9\<rparr> 2 (Application_Value 17))"
  by (simp add: query6_g0_core_def code_source_nonreceipt_read_service_def
      code_decode_query_nonreceipt_def decode_wire_query_body_def parse_wire_application_query_def Let_def)

lemma query6_g0_source_uses_the_capture_boundary:
  "query6_capture_from_core fallback 7 query6_g0_core facts provider upstream product_state =
    query6_capture_boundary fallback 7 query6_g0_scope facts provider upstream product_state"
  unfolding query6_capture_from_core_def
  apply (subst query6_g0_selected_service)
  by (simp add: query6_g0_core_def query6_g0_scope_def)

lemma query6_g0_grant_matrix:
  "query6_capture_boundary False 7 query6_g0_scope (query6_g0_facts [17] []) 100
    (Current_Cut_Value query6_g0_cut (Units_Value 0)) state = (state, Q6_Cache_Value query6_g0_entry)"
  "query6_capture_boundary False 7 query6_g0_scope (query6_g0_facts [] [17]) 100
    (Current_Cut_Value query6_g0_cut (Units_Value 0)) state = (state, Q6_Endpoint_Rejected)"
  "query6_capture_boundary False 7 query6_g0_scope (query6_g0_facts [17] [17]) 100
    (Current_Cut_Value query6_g0_cut (Units_Value 0)) state = (state, Q6_Cache_Value query6_g0_entry)"
  "query6_capture_boundary False 7 query6_g0_scope (query6_g0_facts [] []) 100
    (Current_Cut_Value query6_g0_cut (Units_Value 0)) state = (state, Q6_Endpoint_Rejected)"
  "query6_capture_boundary False 7 query6_g0_scope (query6_g0_facts [18] [18]) 100
    (Current_Cut_Value query6_g0_cut (Units_Value 0)) state = (state, Q6_Endpoint_Rejected)"
  by (simp_all add: query6_capture_boundary_def query6_auth_matches_def query6_capture_permission_def
      query6_g0_facts_def query6_g0_scope_def query6_g0_entry_def)

lemma query6_g0_only_current_fallback_changes_the_current_only_case:
  "query6_capture_boundary False 7 query6_g0_scope (query6_g0_facts [] [17]) 100
    (Current_Cut_Value query6_g0_cut (Units_Value 0)) state = (state, Q6_Endpoint_Rejected)"
  "query6_capture_boundary True 7 query6_g0_scope (query6_g0_facts [] [17]) 100
    (Current_Cut_Value query6_g0_cut (Units_Value 0)) state = (state, Q6_Cache_Value query6_g0_entry)"
  by (simp_all add: query6_capture_boundary_def query6_auth_matches_def query6_capture_permission_def
      query6_g0_facts_def query6_g0_scope_def query6_g0_entry_def)

thm_oracles query6_exact_capture_selector_is_reused query6_capture_is_product_pure
  query6_success_uses_capture_grant_and_exact_scope query6_g0_grant_matrix
  query6_g0_only_current_fallback_changes_the_current_only_case

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms query6_exact_capture_selector_is_reused
    query6_capture_is_product_pure query6_success_uses_capture_grant_and_exact_scope
    query6_g0_grant_matrix query6_g0_only_current_fallback_changes_the_current_only_case})
  then () else error "Unexpected oracle in QUERY6 capture G0"
\<close>

end
