theory Pending_Lock_Seeds
  imports Pending_Lock_Model
begin

datatype pl_setup = PL_Setup_Record nat pl_evidence_kind | PL_Setup_Credit nat
  | PL_Setup_Time nat | PL_Setup_Preempt nat nat nat

record pl_case =
  plcase_id :: nat
  plcase_binding :: pl_binding
  plcase_initial :: nat
  plcase_epoch :: nat
  plcase_lease :: nat
  plcase_setup :: "pl_setup list"
  plcase_command :: pl_command
  plcase_actor :: nat
  plcase_session :: nat
  plcase_credential :: "pl_credential option"

definition pl_seed_grants where
  "pl_seed_grants = concat (map (\<lambda>actor. concat (map (\<lambda>route.
      map (\<lambda>permission. (actor,route,permission)) [0,1,2,3,4,5,6]) [0,1,2])) [7,8])"

definition pl_pending_seed where
  "pl_pending_seed binding initial epoch lease =
    (if pl_amount binding = 0 \<or> initial < pl_amount binding \<or> initial \<ge> 2^64 \<or>
        lease = 0 \<or> lease \<ge> 2^64 then None else
     Some \<lparr>pls_binding = binding,pls_exists = True,pls_epoch = epoch,pls_revision = 3,pls_clock = 0,
       pls_holder = 7,pls_generation = 0,pls_expires = lease,pls_phase = PL_Pending,
       pls_footprint = [pl_asset binding],pls_active = [(pl_asset binding,pl_origin binding)],
       pls_versions = [(pl_asset binding,0)],pls_assets = [pl_asset binding],
       pls_contexts = [fst (pl_origin binding),pl_destination binding],
       pls_sessions = [(1,(7,epoch)),(2,(8,epoch))],pls_grants = pl_seed_grants,pls_connected = True,
       pls_terminal = None,pls_evidence = [],pls_source = initial - pl_amount binding,
       pls_destination_balance = 0,pls_root_funding = 0\<rparr>)"

definition pl_seed_credential where
  "pl_seed_credential binding holder generation epoch =
    \<lparr>plc_asset = pl_asset binding,plc_origin = pl_origin binding,plc_holder = holder,
      plc_generation = generation,plc_epoch = epoch\<rparr>"

definition pl_fresh_request where
  "pl_fresh_request state actor session command credential =
    \<lparr>plr_binding = pls_binding state,plr_actor = actor,plr_caller = actor,plr_session = session,
      plr_endpoint = fst (pl_origin (pls_binding state)),plr_cut_epoch = pls_epoch state,
      plr_cut_revision = pls_revision state,plr_route = 0,plr_verified = True,
      plr_credential = credential,plr_versions = [],plr_command = command\<rparr>"

definition pl_prefix_authorized where
  "pl_prefix_authorized state endpoint permission \<longleftrightarrow>
    pls_connected state \<and> Suc (pls_revision state) < 2^64 \<and>
    pl_asset (pls_binding state) \<in> set (pls_assets state) \<and>
    endpoint \<in> set (pls_contexts state) \<and> pl_destination (pls_binding state) \<in> set (pls_contexts state) \<and>
    map_of (pls_sessions state) 1 = Some (7,pls_epoch state) \<and> (7,0,permission) \<in> set (pls_grants state)"

definition pl_prefix_record where
  "pl_prefix_record reference kind state =
    (if \<not> pl_prefix_authorized state (fst (pl_origin (pls_binding state))) 5 \<or>
        \<not> pls_exists state \<or> map_of (pls_evidence state) reference \<noteq> None then None
     else let admissible = (case pls_terminal state of None \<Rightarrow> pls_phase state = PL_Pending
          | Some primary \<Rightarrow> case map_of (pls_evidence state) primary of None \<Rightarrow> False
             | Some (binding,original_kind) \<Rightarrow> original_kind = kind)
      in if \<not> admissible then None else
        Some (state\<lparr>pls_terminal := (case pls_terminal state of None \<Rightarrow> Some reference | Some primary \<Rightarrow> Some primary),
          pls_evidence := (reference,(pls_binding state,kind)) # pls_evidence state,
          pls_revision := Suc (pls_revision state)\<rparr>))"

definition pl_prefix_credit where
  "pl_prefix_credit reference epoch state =
    (let token = pl_seed_credential (pls_binding state) 7 0 epoch;
         request = pl_fresh_request state 7 1 (PL_Reconcile 0 reference) (Some token)
     in if \<not> pl_prefix_authorized state (pl_destination (pls_binding state)) 6 \<or>
        \<not> pl_bound_credential request state 0 \<or>
        map_of (pls_active state) (pl_asset (pls_binding state)) \<noteq> Some (pl_origin (pls_binding state)) \<or>
        pls_phase state \<noteq> PL_Pending \<or> \<not> pl_exact_confirmed state reference \<or>
        pls_destination_balance state + pl_amount (pls_binding state) \<ge> 2^64 then None
      else Some (state\<lparr>pls_phase := PL_Credited,
        pls_destination_balance := pls_destination_balance state + pl_amount (pls_binding state),
        pls_root_funding := pl_amount (pls_binding state),pls_revision := Suc (pls_revision state)\<rparr>))"

fun pl_setup_one :: "nat \<Rightarrow> pl_setup \<Rightarrow> pl_state \<Rightarrow> pl_state option" where
  "pl_setup_one epoch (PL_Setup_Record reference kind) state = pl_prefix_record reference kind state"
| "pl_setup_one epoch (PL_Setup_Credit reference) state = pl_prefix_credit reference epoch state"
| "pl_setup_one epoch (PL_Setup_Time elapsed) state =
    (let result = pl_step True (pl_fresh_request state 7 1 (PL_Time elapsed) None) state
     in if snd result = PL_Rejected then None else Some (fst result))"
| "pl_setup_one epoch (PL_Setup_Preempt actor session duration) state =
    (let result = pl_step True (pl_fresh_request state actor session (PL_Preempt duration) None) state
     in if snd result = PL_Rejected then None else Some (fst result))"

fun pl_run_setup :: "nat \<Rightarrow> pl_setup list \<Rightarrow> pl_state \<Rightarrow> pl_state option" where
  "pl_run_setup epoch [] state = Some state"
| "pl_run_setup epoch (operation # rest) state =
    Option.bind (pl_setup_one epoch operation state) (pl_run_setup epoch rest)"

definition pl_case_before where
  "pl_case_before item = Option.bind
    (pl_pending_seed (plcase_binding item) (plcase_initial item) (plcase_epoch item) (plcase_lease item))
    (pl_run_setup (plcase_epoch item) (plcase_setup item))"

definition pl_case_request where
  "pl_case_request item state = pl_fresh_request state (plcase_actor item) (plcase_session item)
    (plcase_command item) (plcase_credential item)"

definition pl_run_case where
  "pl_run_case require_credit item = map_option (\<lambda>before.
    let request = pl_case_request item before; (after,reply) = pl_step require_credit request before
    in (before,request,after,reply)) (pl_case_before item)"

text \<open>
  The pending seed is a declared typed projection of successful admitted
  Reserve(lease), Dispatch(0), Debit(0): holder 7, generation 0, clock 0,
  revision 3, source initial-minus-amount and no destination credit. It is not
  a signed Packet or a proof of a complete reference prefix. A later source
  observer must execute that prefix and compare the entire before projection.
  The two finite prefix helpers mirror admitted native RecordTerminal/Credit
  for this fixture. Their evidence binding is the fixed slot binding; callback
  truth is the named trusted-fixture boundary. Credit has no expiry/version
  gate, as in production. Prefix rejection is metadata None, never a target
  protocol result. The Reconcile-shaped request in the Credit helper is used
  only for common bound-credential fields, not for an effect or authorization.
\<close>

lemma pl_credit_prefix_preserves_the_active_lock:
  assumes "pl_prefix_credit reference epoch state = Some after"
  shows "pls_active after = pls_active state" "pls_holder after = pls_holder state"
    "pls_generation after = pls_generation state" "pls_expires after = pls_expires state"
  using assms by (auto simp: pl_prefix_credit_def Let_def split: if_splits)

lemma pl_setup_failure_never_becomes_a_target_reply:
  "pl_case_before item = None \<Longrightarrow> pl_run_case require_credit item = None"
  by (simp add: pl_run_case_def)

end
