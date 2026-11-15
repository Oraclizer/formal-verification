theory Open_Scheduler
  imports REOS_Rollback.Rollback_Contracts
begin

datatype packet_body =
    Ordinary_Work nat
  | Raise_Level nat nat
  | Lower_Level nat nat
  | Execute_Governed_Rollback rollback_intent "nat option" "nat option"

record packet =
  packet_identity :: nat
  packet_contents :: packet_body
  packet_authority_epoch :: nat
  packet_policy_epoch :: nat
  packet_order :: nat

fun regulatory_case :: "packet_body \<Rightarrow> nat" where
  "regulatory_case (Ordinary_Work instruction) = 0"
| "regulatory_case (Raise_Level k level) = k"
| "regulatory_case (Lower_Level k level) = k"
| "regulatory_case (Execute_Governed_Rollback r a p) = request_case r"

fun ordinary_body :: "packet_body \<Rightarrow> bool" where
  "ordinary_body (Ordinary_Work instruction) = True"
| "ordinary_body _ = False"

record scheduler_state =
  rollback_context :: rollback_state
  signed_packets :: "packet set"
  regulatory_grants :: "packet set"
  verified_context_updates :: "(nat \<times> nat \<times> nat \<times> nat) set"
  ordinary_queue :: "packet list"
  regulatory_queue :: "packet list"
  dedup_ids :: "nat set"
  ordinary_receipts :: "nat \<Rightarrow> packet option"
  regulation_receipts :: "nat \<Rightarrow> packet option"
  severity_now :: "nat \<Rightarrow> nat"
  severity_limit :: "nat \<Rightarrow> nat"

datatype scheduler_action =
    Submit packet
  | Honest_Service
  | Unproductive_Turn
  | Rotate_Context nat nat nat nat

datatype scheduler_denial =
    Signature_Failed | Reused_ID | Packet_Stale | Regulation_Ineligible
  | Empty_Queue | Invalid_Update

datatype scheduler_fault = No_Effective_Opportunity | Invalid_Queue_State
datatype scheduler_effect = Served_Ordinary nat | Served_Regulation nat nat | Snapshot_Changed
type_synonym scheduler_result = "(nat,scheduler_denial,scheduler_fault,scheduler_effect) transition_result"

text \<open>Authenticated packets, regulatory grants, priority keys and admitted
  context updates are outputs of the verified-input interface. The ordinary
  queue holds admitted work in FIFO order. A smaller priority key goes first
  among eligible regulatory packets. The runtime must justify the key
  encoding against its authority and ordering policy.\<close>

definition packet_fresh :: "scheduler_state \<Rightarrow> packet \<Rightarrow> bool"
where
  "packet_fresh s p =
    (packet_authority_epoch p = authority_epoch (rollback_context s)
     \<and> packet_policy_epoch p = policy_epoch (rollback_context s) (regulatory_case (packet_contents p)))"

fun apply_regulation ::
  "scheduler_state \<Rightarrow> packet \<Rightarrow> packet_body \<Rightarrow> scheduler_state option"
where
  "apply_regulation s p (Ordinary_Work instruction) = None"
| "apply_regulation s p (Raise_Level k level) =
    (if p \<in> regulatory_grants s \<and> severity_now s k < level \<and> level \<le> severity_limit s k
     then Some (s\<lparr>severity_now := (severity_now s)(k := level)\<rparr>) else None)"
| "apply_regulation s p (Lower_Level k level) =
    (if p \<in> regulatory_grants s \<and> level < severity_now s k
     then Some (s\<lparr>severity_now := (severity_now s)(k := level)\<rparr>) else None)"
| "apply_regulation s p (Execute_Governed_Rollback r a pf) =
    (if packet_identity p \<noteq> request_id r then None
     else case Rollback_Model.execute (rollback_context s) (Execute_Rollback r a pf) of
        (Accepted txn, u) \<Rightarrow> Some (s\<lparr>rollback_context := u\<rparr>)
      | _ \<Rightarrow> None)"

definition regulatory_effect :: "scheduler_state \<Rightarrow> packet \<Rightarrow> scheduler_state option"
where
  "regulatory_effect s p =
    (if p \<in> signed_packets s \<and> packet_fresh s p
     then apply_regulation s p (packet_contents p) else None)"

definition ready_regulation :: "scheduler_state \<Rightarrow> packet \<Rightarrow> bool"
where
  "ready_regulation s p \<longleftrightarrow> regulatory_effect s p \<noteq> None"

definition priority_slots :: "scheduler_state \<Rightarrow> nat"
where
  "priority_slots s = length (filter (ready_regulation s) (regulatory_queue s))"

definition next_regulation :: "scheduler_state \<Rightarrow> packet option"
where
  "next_regulation s = List.find (ready_regulation s) (sort_key packet_order (regulatory_queue s))"

fun first_ready_effect ::
  "scheduler_state \<Rightarrow> packet list \<Rightarrow> (packet \<times> scheduler_state) option"
where
  "first_ready_effect s [] = None"
| "first_ready_effect s (p # ps) =
    (case regulatory_effect s p of
       None \<Rightarrow> first_ready_effect s ps
     | Some u \<Rightarrow> Some (p,u))"

lemma first_ready_effect_exact:
  "first_ready_effect s ps = Some (p,u) \<longleftrightarrow>
    List.find (ready_regulation s) ps = Some p \<and> regulatory_effect s p = Some u"
  by (induction ps) (auto simp: ready_regulation_def split: option.splits)

lemma first_ready_effect_absent:
  "first_ready_effect s ps = None \<longleftrightarrow> List.find (ready_regulation s) ps = None"
  by (induction ps) (auto simp: ready_regulation_def split: option.splits)

definition enqueue_packet :: "scheduler_state \<Rightarrow> packet \<Rightarrow> scheduler_state"
where
  "enqueue_packet s p =
    (let seen = insert (packet_identity p) (dedup_ids s) in
     if ordinary_body (packet_contents p)
     then s\<lparr>dedup_ids := seen, ordinary_queue := ordinary_queue s @ [p]\<rparr>
     else s\<lparr>dedup_ids := seen, regulatory_queue := regulatory_queue s @ [p]\<rparr>)"

definition admit :: "scheduler_state \<Rightarrow> packet \<Rightarrow> scheduler_result \<times> scheduler_state"
where
  "admit s p =
    (if p \<notin> signed_packets s then (Rejected Signature_Failed, s)
     else if packet_identity p \<in> dedup_ids s then (Rejected Reused_ID, s)
     else if \<not> packet_fresh s p then (Rejected Packet_Stale, s)
     else if \<not> ordinary_body (packet_contents p) \<and> \<not> ready_regulation s p
          then (Rejected Regulation_Ineligible, s)
     else (Accepted (packet_identity p), enqueue_packet s p))"

definition serve_ordinary :: "scheduler_state \<Rightarrow> scheduler_result \<times> scheduler_state"
where
  "serve_ordinary s =
    (case ordinary_queue s of [] \<Rightarrow> (Rejected Empty_Queue, s)
     | p # rest \<Rightarrow>
       if ordinary_body (packet_contents p)
       then (Internal (Served_Ordinary (packet_identity p)), s\<lparr>
          ordinary_queue := rest, ordinary_receipts := (ordinary_receipts s)(packet_identity p \<mapsto> p)\<rparr>)
       else (Operational_Failure Invalid_Queue_State, s))"

definition schedule :: "scheduler_state \<Rightarrow> scheduler_result \<times> scheduler_state"
where
  "schedule s =
    (case first_ready_effect s (sort_key packet_order (regulatory_queue s)) of
       None \<Rightarrow> serve_ordinary s
     | Some (p,u) \<Rightarrow>
        (Internal (Served_Regulation (packet_identity p) (regulatory_case (packet_contents p))), u\<lparr>
           regulatory_queue := remove1 p (regulatory_queue s),
           regulation_receipts := (regulation_receipts s)(packet_identity p \<mapsto> p)\<rparr>))"

lemma schedule_contract:
  "schedule s =
    (case next_regulation s of
       None \<Rightarrow> serve_ordinary s
     | Some p \<Rightarrow>
       (case regulatory_effect s p of
          None \<Rightarrow> (Operational_Failure Invalid_Queue_State, s)
        | Some u \<Rightarrow>
          (Internal (Served_Regulation (packet_identity p) (regulatory_case (packet_contents p))), u\<lparr>
             regulatory_queue := remove1 p (regulatory_queue s),
             regulation_receipts := (regulation_receipts s)(packet_identity p \<mapsto> p)\<rparr>)))"
proof (cases "next_regulation s")
  case None
  then have "first_ready_effect s (sort_key packet_order (regulatory_queue s)) = None"
    by (simp add: first_ready_effect_absent next_regulation_def)
  with None show ?thesis by (simp add: schedule_def)
next
  case (Some p)
  then have "ready_regulation s p" by (auto simp: next_regulation_def find_Some_iff)
  then obtain u where effect: "regulatory_effect s p = Some u"
    by (auto simp: ready_regulation_def)
  from Some effect have "first_ready_effect s (sort_key packet_order (regulatory_queue s)) = Some (p,u)"
    by (simp add: first_ready_effect_exact next_regulation_def)
  with Some effect show ?thesis by (simp add: schedule_def)
qed

fun run_scheduler :: "scheduler_state \<Rightarrow> scheduler_action \<Rightarrow> scheduler_result \<times> scheduler_state"
where
  "run_scheduler s (Submit p) = admit s p"
| "run_scheduler s Honest_Service = schedule s"
| "run_scheduler s Unproductive_Turn = (Operational_Failure No_Effective_Opportunity, s)"
| "run_scheduler s (Rotate_Context time a k policy) =
    (if (time,a,k,policy) \<notin> verified_context_updates s then (Rejected Invalid_Update, s)
     else case Rollback_Model.execute (rollback_context s) (Advance_Context time a k policy) of
        (Internal Context_Advanced, u) \<Rightarrow> (Internal Snapshot_Changed, s\<lparr>rollback_context := u\<rparr>)
      | _ \<Rightarrow> (Rejected Invalid_Update, s))"

definition scheduler_step :: "(scheduler_state,scheduler_action,scheduler_result) step_rel"
where
  "scheduler_step s action outcome t \<longleftrightarrow> run_scheduler s action = (outcome,t)"

definition waiting :: "nat \<Rightarrow> scheduler_state \<Rightarrow> bool"
where
  "waiting q s \<longleftrightarrow> (\<exists>p \<in> set (ordinary_queue s). packet_identity p = q)"

definition earlier_ordinary :: "nat \<Rightarrow> scheduler_state \<Rightarrow> nat"
where
  "earlier_ordinary q s = length (takeWhile (\<lambda>p. packet_identity p \<noteq> q) (ordinary_queue s))"

definition ordinary_shape :: "scheduler_state \<Rightarrow> bool"
where
  "ordinary_shape s \<longleftrightarrow> (\<forall>p \<in> set (ordinary_queue s). ordinary_body (packet_contents p))"

definition served_ordinary ::
  "nat \<Rightarrow> (scheduler_state,scheduler_action,scheduler_result) transition \<Rightarrow> bool"
where
  "served_ordinary q e \<longleftrightarrow>
    step_action e = Honest_Service \<and> step_outcome e = Internal (Served_Ordinary q)"

definition spends_priority ::
  "(scheduler_state,scheduler_action,scheduler_result) transition \<Rightarrow> bool"
where
  "spends_priority e \<longleftrightarrow> (\<exists>q k. step_outcome e = Internal (Served_Regulation q k))"

end
