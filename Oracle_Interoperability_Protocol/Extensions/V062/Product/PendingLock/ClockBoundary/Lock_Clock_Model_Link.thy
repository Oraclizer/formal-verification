theory Lock_Clock_Model_Link
  imports "OIP_Pending_Lock_Export.Pending_Lock_Export"
begin

text \<open>
  The input boundary carries a complete Pending Lock state and request. The
  normal transition and the reply, state and gate views come from the parent
  sessions. A malformed integer argument has no model result.
\<close>

definition pl_clock_u64 :: "integer \<Rightarrow> bool" where
  "pl_clock_u64 word \<longleftrightarrow> 0 \<le> word \<and> word < 18446744073709551616"

definition pl_clock_matrix_u64 :: "integer list list list \<Rightarrow> bool" where
  "pl_clock_matrix_u64 rows \<longleftrightarrow> list_all (list_all (list_all pl_clock_u64)) rows"

definition pl_clock_flag :: "nat \<Rightarrow> bool option" where
  "pl_clock_flag word = (if word = 0 then Some False else if word = 1 then Some True else None)"

definition pl_clock_phase :: "nat \<Rightarrow> pl_phase option" where
  "pl_clock_phase word =
    (let phases = [PL_Held,PL_Dispatched,PL_Pending,PL_Credited,PL_Reconciled,PL_Refunded,PL_Closed]
     in if word < length phases then Some (phases ! word) else None)"

definition pl_clock_binding :: "nat list \<Rightarrow> pl_binding option" where
  "pl_clock_binding words =
    (case words of [domain,event,asset,owner,destination,recipient,amount] \<Rightarrow>
      Some \<lparr>pl_origin = (domain,event),pl_asset = asset,pl_owner = owner,
        pl_destination = destination,pl_recipient = recipient,pl_amount = amount\<rparr>
    | _ \<Rightarrow> None)"

definition pl_clock_credential :: "nat list \<Rightarrow> pl_credential option option" where
  "pl_clock_credential words =
    (case words of [] \<Rightarrow> Some None
    | [asset,domain,event,holder,generation,epoch] \<Rightarrow>
      Some (Some \<lparr>plc_asset = asset,plc_origin = (domain,event),plc_holder = holder,
        plc_generation = generation,plc_epoch = epoch\<rparr>)
    | _ \<Rightarrow> None)"

definition pl_clock_terminal :: "nat list \<Rightarrow> nat option option" where
  "pl_clock_terminal words =
    (case words of [] \<Rightarrow> Some None | [reference] \<Rightarrow> Some (Some reference) | _ \<Rightarrow> None)"

fun pl_clock_pairs :: "nat list list \<Rightarrow> (nat \<times> nat) list option" where
  "pl_clock_pairs [] = Some []"
| "pl_clock_pairs (words # rows) =
    (case (words,pl_clock_pairs rows) of ([key,value],Some rest) \<Rightarrow> Some ((key,value) # rest)
    | _ \<Rightarrow> None)"

fun pl_clock_triples :: "nat list list \<Rightarrow> (nat \<times> nat \<times> nat) list option" where
  "pl_clock_triples [] = Some []"
| "pl_clock_triples (words # rows) =
    (case (words,pl_clock_triples rows) of ([key,left,right],Some rest) \<Rightarrow> Some ((key,left,right) # rest)
    | _ \<Rightarrow> None)"

fun pl_clock_evidence :: "nat list list \<Rightarrow> (nat \<times> (pl_binding \<times> pl_evidence_kind)) list option" where
  "pl_clock_evidence [] = Some []"
| "pl_clock_evidence (words # rows) =
    (case words of reference # kind # body \<Rightarrow>
      (case (pl_clock_binding body,pl_clock_evidence rows) of
        (Some binding,Some rest) \<Rightarrow>
          if kind = 1 then Some ((reference,(binding,PL_Confirmed)) # rest)
          else if kind = 2 then Some ((reference,(binding,PL_Reversed)) # rest) else None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

definition pl_clock_command :: "nat list \<Rightarrow> pl_command option" where
  "pl_clock_command words =
    (case words of [tag,value,reference] \<Rightarrow>
      if tag = 4 then Some (PL_Reconcile value reference)
      else if reference \<noteq> 0 then None
      else if tag = 0 then Some (PL_Cancel value)
      else if tag = 1 then Some (PL_Fence value)
      else if tag = 2 then Some (PL_Preempt value)
      else if tag = 3 then Some (PL_Time value) else None
    | _ \<Rightarrow> None)"

definition pl_clock_parse_state :: "nat list list list \<Rightarrow> pl_state option" where
  "pl_clock_parse_state rows =
    (case rows of
      [[binding],[[exists,epoch,revision,clock,holder,generation,expires,phase,connected,source,destination,funding]],
       [footprint],[assets],[contexts],[terminal],active,versions,sessions,grants,evidence] \<Rightarrow>
        (case (pl_clock_binding binding,pl_clock_flag exists,pl_clock_phase phase,pl_clock_flag connected,
               pl_clock_terminal terminal,pl_clock_triples active,pl_clock_pairs versions,
               pl_clock_triples sessions,pl_clock_triples grants,pl_clock_evidence evidence) of
          (Some bound,Some present,Some phase_value,Some connection,Some terminal_value,
           Some active_rows,Some version_rows,Some session_rows,Some grant_rows,Some evidence_rows) \<Rightarrow>
            Some \<lparr>pls_binding = bound,pls_exists = present,pls_epoch = epoch,pls_revision = revision,
              pls_clock = clock,pls_holder = holder,pls_generation = generation,pls_expires = expires,
              pls_phase = phase_value,pls_footprint = footprint,pls_active = active_rows,
              pls_versions = version_rows,pls_assets = assets,pls_contexts = contexts,
              pls_sessions = session_rows,pls_grants = grant_rows,pls_connected = connection,
              pls_terminal = terminal_value,pls_evidence = evidence_rows,pls_source = source,
              pls_destination_balance = destination,pls_root_funding = funding\<rparr>
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

definition pl_clock_parse_request :: "nat list list list \<Rightarrow> pl_request option" where
  "pl_clock_parse_request rows =
    (case rows of [[binding],[[actor,caller,session,endpoint,epoch,revision,route,verified]],
                   [command],[credential],versions] \<Rightarrow>
      (case (pl_clock_binding binding,pl_clock_flag verified,pl_clock_command command,
             pl_clock_credential credential,pl_clock_pairs versions) of
        (Some bound,Some verification,Some command_value,Some credential_value,Some version_rows) \<Rightarrow>
          Some \<lparr>plr_binding = bound,plr_actor = actor,plr_caller = caller,plr_session = session,
            plr_endpoint = endpoint,plr_cut_epoch = epoch,plr_cut_revision = revision,plr_route = route,
            plr_verified = verification,plr_credential = credential_value,plr_versions = version_rows,
            plr_command = command_value\<rparr>
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

definition pl_clock_result :: "pl_state \<Rightarrow> pl_request \<Rightarrow> (pl_state \<times> pl_reply) \<Rightarrow> pl_integer_result" where
  "pl_clock_result initial request result =
    (case result of (next,reply) \<Rightarrow>
      (map integer_of_nat [pl_reply_word reply,pl_bit (initial = next)],
       pl_request_view request,pl_state_view initial,pl_state_view next,
       pl_gate_view request initial,pl_gate_view request next))"

definition pl_clock_submit_integer :: "integer list list list \<Rightarrow> integer list list list \<Rightarrow> pl_integer_result option" where
  "pl_clock_submit_integer state_words request_words =
    (if \<not> pl_clock_matrix_u64 state_words \<or> \<not> pl_clock_matrix_u64 request_words then None
     else case (pl_clock_parse_state (map (map (map nat_of_integer)) state_words),
                pl_clock_parse_request (map (map (map nat_of_integer)) request_words)) of
       (Some initial,Some request) \<Rightarrow> Some (pl_clock_result initial request (pl_step True request initial))
     | _ \<Rightarrow> None)"

lemma pl_clock_submit_uses_parent_transition:
  assumes "pl_clock_matrix_u64 state_words" "pl_clock_matrix_u64 request_words"
    "pl_clock_parse_state (map (map (map nat_of_integer)) state_words) = Some initial"
    "pl_clock_parse_request (map (map (map nat_of_integer)) request_words) = Some request"
  shows "pl_clock_submit_integer state_words request_words =
    Some (pl_clock_result initial request (pl_step True request initial))"
  using assms by (simp add: pl_clock_submit_integer_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms pl_clock_submit_uses_parent_transition})
  then () else error "Unexpected oracle in Pending Lock input export"
\<close>

export_code pl_clock_submit_integer
  in SML module_name OIP_Lock_Clock_Model_Link file_prefix "oip_lock_clock_model_link"

end
