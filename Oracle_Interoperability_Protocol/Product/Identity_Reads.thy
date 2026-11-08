theory Identity_Reads
  imports Identity_Endpoints
begin

section \<open>All exposed observations pass current authorization\<close>

datatype identity_read_request =
    Current_Data application_query product_cut
  | Historical_Data application_query nat
  | Raw_Data application_query
  | Operation_Status source_key
  | Authority_Journal
  | Owner_Data product_asset

datatype identity_read_reply =
    Authorized_Data product_read_reply
  | Authorized_Raw application_value
  | Authorized_Operation "reservation_phase option" nat "product_origin_decision option" bool
  | Authorized_Journal "client_call_id list"
  | Authorized_Owner "product_principal option"
  | Identity_Read_Rejected
  | Identity_Read_Unavailable

definition identity_read_allowed where
  "identity_read_allowed directory policy authenticate verify_read token proof target request source \<longleftrightarrow>
    (\<exists>identity. authenticate token = Some identity \<and>
      active_identity directory identity proof source \<and>
      verify_read identity proof target request \<and>
      policy identity target request (proof_epoch proof))"

context source_attestation
begin

fun authorized_read_value where
  "authorized_read_value identity proof target (Current_Data query expected) reads =
    Authorized_Data (read_current_product (\<lambda>_ _ _. True) (identity_principal identity) (proof_session proof) query expected reads)"
| "authorized_read_value identity proof target (Historical_Data query revision) reads =
    Authorized_Data (read_historical_product (\<lambda>_ _ _. True) (identity_principal identity) (proof_session proof) query revision reads)"
| "authorized_read_value identity proof target (Raw_Data query) reads =
    (if read_asset_registered query reads
     then Authorized_Raw (stored_query query (capture_snapshot (authoritative_read_core (read_authority reads))))
     else Identity_Read_Unavailable)"
| "authorized_read_value identity proof target (Operation_Status key) reads =
    (let authority = read_authority reads; core = authoritative_read_core authority;
         reservations = machine_state (core_parent core);
         pending = (case reservation_at reservations key of None \<Rightarrow> 0
           | Some claim \<Rightarrow> let binding = reservation_binding claim in
               if binding \<in> unresolved_source_obligations reservations then binding_amount binding else 0)
     in Authorized_Operation (phase_at reservations key) pending
       (origin_decisions (settlement_primary authority) key) (key \<in> core_published core))"
| "authorized_read_value identity proof target Authority_Journal reads =
    (let authority = read_authority reads; requests = product_requests (product_durable (observed_product_source authority));
         visible = (\<lambda>call_id. fst call_id = identity_principal identity \<and>
           (\<exists>envelope. requests call_id = Some envelope \<and> command_target envelope (envelope_command envelope) = target))
     in Authorized_Journal (filter visible (authority_execution_ids (call_authority_log (exact_calls authority)))))"
| "authorized_read_value identity proof target (Owner_Data asset) reads =
    Authorized_Owner (product_owners (product_durable (observed_product_source (read_authority reads))) asset)"

definition read_at_identity_endpoint where
  "read_at_identity_endpoint directory policy authenticate verify_read token proof target request s =
    (if \<not> identity_read_allowed directory policy authenticate verify_read token proof target request (identity_source s)
     then Identity_Read_Rejected
     else let reads = regulated_read_world s in
       if \<not> read_authority_available reads then Identity_Read_Unavailable
       else case authenticate token of None \<Rightarrow> Identity_Read_Rejected
         | Some identity \<Rightarrow> authorized_read_value identity proof target request reads)"

definition capture_at_identity_endpoint where
  "capture_at_identity_endpoint directory policy authenticate verify_read token proof target query s =
    (let reads = regulated_read_world s; expected = observed_product_cut (read_authority reads);
         request = Current_Data query expected
     in if identity_read_allowed directory policy authenticate verify_read token proof target request (identity_source s)
       then case authenticate token of None \<Rightarrow> s
        | Some identity \<Rightarrow> replace_regulated_reads
            (capture_product_cache (\<lambda>_ _ _. True) (identity_principal identity) (proof_session proof) query reads) s
       else s)"

lemma denied_current_access_cannot_produce_a_cache_entry:
  assumes "\<not> identity_read_allowed directory policy authenticate verify_read token proof target
    (Current_Data query (observed_product_cut (read_authority (regulated_read_world s)))) (identity_source s)"
  shows "capture_at_identity_endpoint directory policy authenticate verify_read token proof target query s = s"
  using assms by (simp add: capture_at_identity_endpoint_def Let_def)

theorem every_unauthorized_read_has_the_same_refusal:
  assumes "\<not> identity_read_allowed directory policy authenticate verify_read token proof target request (identity_source s)"
  shows "read_at_identity_endpoint directory policy authenticate verify_read token proof target request s = Identity_Read_Rejected"
  using assms by (simp add: read_at_identity_endpoint_def)

lemma a_live_authorized_raw_read_observes_the_actual_current_source:
  assumes "authenticate token = Some identity"
    "identity_read_allowed directory policy authenticate verify_read token proof target (Raw_Data query) (identity_source s)"
    "read_authority_available (regulated_read_world s)"
    "read_asset_registered query (regulated_read_world s)"
  shows "read_at_identity_endpoint directory policy authenticate verify_read token proof target (Raw_Data query) s =
    Authorized_Raw (stored_query query (capture_snapshot (authoritative_read_core (read_authority (regulated_read_world s)))))"
  using assms by (simp add: read_at_identity_endpoint_def Let_def)

lemma raw_read_of_an_unregistered_asset_cannot_expose_a_value:
  assumes "\<not> read_asset_registered query (regulated_read_world s)"
  shows "read_at_identity_endpoint directory policy authenticate verify_read token proof target (Raw_Data query) s
    \<noteq> Authorized_Raw result"
  using assms by (auto simp: read_at_identity_endpoint_def Let_def split: option.splits if_splits)

lemma authorized_owner_read_uses_the_same_committed_token_owner:
  assumes "authenticate token = Some identity"
    "identity_read_allowed directory policy authenticate verify_read token proof target (Owner_Data asset) (identity_source s)"
    "read_authority_available (regulated_read_world s)"
  shows "read_at_identity_endpoint directory policy authenticate verify_read token proof target (Owner_Data asset) s =
    Authorized_Owner (product_owners (product_durable (identity_source s)) asset)"
  using assms by (simp add: read_at_identity_endpoint_def identity_source_def Let_def)

lemma journal_cannot_disclose_a_foreign_namespace:
  assumes "read_at_identity_endpoint directory policy authenticate verify_read token proof target Authority_Journal s = Authorized_Journal ids"
    "authenticate token = Some identity" "call_id \<in> set ids"
  shows "fst call_id = identity_principal identity"
  using assms by (auto simp: read_at_identity_endpoint_def Let_def split: if_splits)

end

end
