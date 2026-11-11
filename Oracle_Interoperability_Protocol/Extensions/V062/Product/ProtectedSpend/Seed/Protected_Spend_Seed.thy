theory Protected_Spend_Seed
  imports "OIP_Protected_Spend_Core.Protected_Spend_Core"
    "OIP_Reference_Execution.Reference_Read_Code"
begin

record pf_input =
  pf_actor :: nat
  pf_epoch :: nat
  pf_asset :: nat
  pf_source :: nat
  pf_destination :: nat
  pf_root_event :: nat
  pf_freeze_event :: nat
  pf_sender :: nat
  pf_recipient :: nat
  pf_initial :: nat
  pf_root_amount :: nat
  pf_amount :: nat
  pf_jurisdiction :: nat
  pf_basis :: nat
  pf_authorized :: bool

datatype pf_command = PF_Reserve nat | PF_Dispatch nat | PF_Debit nat
  | PF_Record nat | PF_Credit nat | PF_Reconcile nat nat | PF_Publish

record pf_snapshot =
  pf_snapshot_modes :: "((nat \<times> nat) \<times> reg_state) list"
  pf_snapshot_balances :: "((nat \<times> nat \<times> nat) \<times> nat) list"
  pf_snapshot_funding :: "((source_key \<times> (nat \<times> nat \<times> nat)) \<times> nat) list"

record pf_machine =
  pf_input :: pf_input
  pf_state :: ps_state
  pf_history :: "pf_snapshot list"
  pf_trace :: "(nat \<times> nat \<times> nat \<times> nat option \<times> bool) list"

definition pf_root_binding where
  "pf_root_binding p5_input = \<lparr>ps_origin = (pf_source p5_input,pf_root_event p5_input),ps_asset = pf_asset p5_input,
    ps_owner = pf_actor p5_input,ps_destination = pf_destination p5_input,ps_receiver = pf_sender p5_input,
    ps_root_amount = pf_root_amount p5_input\<rparr>"

definition pf_freeze_binding where
  "pf_freeze_binding p5_input = (pf_root_binding p5_input)\<lparr>
    ps_origin := (pf_source p5_input,pf_freeze_event p5_input),ps_root_amount := 0\<rparr>"

definition pf_scope where
  "pf_scope p5_input p5_kind = \<lparr>ps_root = pf_root_binding p5_input,ps_sender = pf_sender p5_input,
    ps_recipient = pf_recipient p5_input,ps_amount = pf_amount p5_input,ps_kind = p5_kind\<rparr>"

definition pf_snapshot where
  "pf_snapshot p5_state = \<lparr>pf_snapshot_modes = ps_modes p5_state,pf_snapshot_balances = ps_balances p5_state,
    pf_snapshot_funding = ps_funding p5_state\<rparr>"

definition pf_grants where
  "pf_grants p5_input = concat (map (\<lambda>p5_route.
      [\<lparr>ps_grant_route = p5_route,ps_grant_actor = pf_actor p5_input,ps_grant_epoch = pf_epoch p5_input,
        ps_grant_scope = pf_scope p5_input PS_Ordinary,ps_grant_jurisdiction = 0,ps_grant_basis = 0\<rparr>] @
      (if pf_authorized p5_input then map (\<lambda>p5_kind.
        \<lparr>ps_grant_route = p5_route,ps_grant_actor = pf_actor p5_input,ps_grant_epoch = pf_epoch p5_input,
          ps_grant_scope = pf_scope p5_input p5_kind,ps_grant_jurisdiction = pf_jurisdiction p5_input,ps_grant_basis = pf_basis p5_input\<rparr>)
          [PS_Recover,PS_Confiscate] else [])) [PS_Normal,PS_Administrative,PS_Adapter,PS_Force_Inclusion])"

definition pf_genesis where
  "pf_genesis p5_input =
    (let p5_root = pf_root_binding p5_input;
         p5_state = \<lparr>ps_epoch = pf_epoch p5_input,ps_revision = 0,ps_clock = 0,ps_up = True,ps_available = True,
           ps_sessions = [(1,(pf_actor p5_input,pf_epoch p5_input))],
           ps_modes = [((pf_source p5_input,pf_asset p5_input),ACTIVE),((pf_destination p5_input,pf_asset p5_input),ACTIVE)],
           ps_balances = [((pf_source p5_input,pf_asset p5_input,pf_actor p5_input),pf_initial p5_input)],ps_funding = [],
           ps_roots = [],ps_reservations = [],ps_active = [],ps_evidence = [],ps_legal_events = [],
           ps_active_freezes = [],ps_active_seizures = [],ps_spend_grants = pf_grants p5_input,
           ps_spend_receipts = [],ps_legal_ids = [],ps_ordinary_ids = [],ps_sync_ids = [],ps_journal = []\<rparr>
     in \<lparr>pf_input = p5_input,pf_state = p5_state,pf_history = [pf_snapshot p5_state],pf_trace = []\<rparr>)"

definition pf_input_domain where
  "pf_input_domain p5_input \<longleftrightarrow> pf_source p5_input \<noteq> pf_destination p5_input \<and>
    pf_root_event p5_input \<noteq> pf_freeze_event p5_input \<and> pf_basis p5_input > 0 \<and>
    list_all (\<lambda>p5_word. p5_word < 2^64) [pf_actor p5_input,pf_epoch p5_input,pf_asset p5_input,
      pf_source p5_input,pf_destination p5_input,pf_root_event p5_input,pf_freeze_event p5_input,
      pf_sender p5_input,pf_recipient p5_input,pf_initial p5_input,pf_root_amount p5_input,pf_amount p5_input,
      pf_jurisdiction p5_input,pf_basis p5_input]"

definition pf_source_account where
  "pf_source_account p5_binding = (fst (ps_origin p5_binding),ps_asset p5_binding,ps_owner p5_binding)"

definition pf_unallocated where
  "pf_unallocated p5_account p5_state = ps_get (ps_balances p5_state) p5_account -
    sum_list (map snd (filter (\<lambda>((p5_origin,p5_holder),p5_value). p5_holder = p5_account) (ps_funding p5_state)))"

definition pf_slot_bound where
  "pf_slot_bound p5_binding p5_generation p5_slot p5_input p5_state \<longleftrightarrow>
    ps_reserved p5_slot = p5_binding \<and> ps_holder p5_slot = pf_actor p5_input \<and>
    ps_generation p5_slot = p5_generation \<and>
    map_of (ps_active p5_state) (ps_asset p5_binding) = Some (ps_origin p5_binding)"

definition pf_store_reservation where
  "pf_store_reservation p5_slot p5_state = p5_state\<lparr>ps_reservations :=
    ps_put (ps_origin (ps_reserved p5_slot)) p5_slot (ps_reservations p5_state)\<rparr>"

definition pf_store_root where
  "pf_store_root p5_slot p5_state = p5_state\<lparr>ps_roots :=
    ps_put (ps_origin (ps_slot_binding p5_slot)) p5_slot (ps_roots p5_state)\<rparr>"

definition pf_ordinary_body where
  "pf_ordinary_body p5_command p5_binding p5_input p5_state =
    (let p5_origin = ps_origin p5_binding; p5_asset = ps_asset p5_binding; p5_amount = ps_root_amount p5_binding in
      if (case p5_command of PF_Dispatch p5_generation \<Rightarrow> True | PF_Debit p5_generation \<Rightarrow> True | _ \<Rightarrow> False)
          \<and> ps_source_protected p5_binding p5_state then (p5_state,1,False)
      else case p5_command of PF_Reserve p5_duration \<Rightarrow>
        if p5_duration = 0 \<or> ps_clock p5_state + p5_duration \<ge> 2^64 \<or>
           map_of (ps_reservations p5_state) p5_origin \<noteq> None \<or> map_of (ps_legal_events p5_state) p5_origin \<noteq> None
        then (p5_state,1,False)
        else if map_of (ps_active p5_state) p5_asset \<noteq> None then (p5_state,2,False)
        else ((pf_store_reservation \<lparr>ps_reserved = p5_binding,ps_holder = pf_actor p5_input,ps_generation = 0,
             ps_expires = ps_clock p5_state + p5_duration,ps_phase = 1,ps_pending = 0\<rparr> p5_state)\<lparr>
             ps_active := ps_put p5_asset p5_origin (ps_active p5_state)\<rparr>,10,True)
      | PF_Publish \<Rightarrow>
        (case map_of (ps_legal_events p5_state) p5_origin of Some p5_event \<Rightarrow>
           if ps_legal_binding p5_event = p5_binding \<and> ps_legal_epoch p5_event = pf_epoch p5_input \<and>
              ps_applied_position p5_event \<noteq> None \<and> ps_legal_published p5_event = None
           then (p5_state\<lparr>ps_legal_events := ps_put p5_origin
             (p5_event\<lparr>ps_legal_published := Some (ps_revision p5_state)\<rparr>) (ps_legal_events p5_state)\<rparr>,22,True)
           else (p5_state,1,False)
         | None \<Rightarrow> case map_of (ps_roots p5_state) p5_origin of None \<Rightarrow> (p5_state,1,False)
           | Some p5_root \<Rightarrow> if ps_slot_binding p5_root = p5_binding \<and> ps_slot_epoch p5_root = pf_epoch p5_input \<and>
                ps_settled p5_root \<noteq> None \<and> ps_published p5_root = None
             then (pf_store_root (p5_root\<lparr>ps_published := Some (ps_revision p5_state)\<rparr>) p5_state,22,True)
             else (p5_state,1,False))
      | _ \<Rightarrow> (case map_of (ps_reservations p5_state) p5_origin of None \<Rightarrow> (p5_state,1,False)
         | Some p5_slot \<Rightarrow> if ps_reserved p5_slot \<noteq> p5_binding then (p5_state,1,False) else
           (case p5_command of
             PF_Dispatch p5_generation \<Rightarrow>
               if pf_slot_bound p5_binding p5_generation p5_slot p5_input p5_state \<and> ps_phase p5_slot = 1 \<and>
                  ps_clock p5_state < ps_expires p5_slot \<and> p5_amount > 0 \<and>
                  p5_amount \<le> pf_unallocated (pf_source_account p5_binding) p5_state
               then (pf_store_reservation (p5_slot\<lparr>ps_phase := 2\<rparr>) p5_state,11,True) else (p5_state,1,False)
           | PF_Debit p5_generation \<Rightarrow>
               if pf_slot_bound p5_binding p5_generation p5_slot p5_input p5_state \<and> ps_phase p5_slot = 2 \<and>
                  ps_clock p5_state < ps_expires p5_slot \<and> p5_amount > 0 \<and> pf_epoch p5_input = ps_epoch p5_state \<and>
                  p5_amount \<le> pf_unallocated (pf_source_account p5_binding) p5_state \<and>
                  map_of (ps_roots p5_state) p5_origin = None \<and> map_of (ps_legal_events p5_state) p5_origin = None
               then let p5_debited = (pf_store_reservation (p5_slot\<lparr>ps_phase := 3,ps_pending := p5_amount\<rparr>) p5_state)\<lparr>
                    ps_balances := ps_put (pf_source_account p5_binding)
                      (ps_get (ps_balances p5_state) (pf_source_account p5_binding) - p5_amount) (ps_balances p5_state)\<rparr>
                 in (pf_store_root \<lparr>ps_slot_binding = p5_binding,ps_slot_epoch = pf_epoch p5_input,
                      ps_decision_kind = None,ps_decision_position = None,ps_settled = None,ps_published = None\<rparr> p5_debited,12,True)
               else (p5_state,1,False)
           | PF_Record p5_reference \<Rightarrow>
               (case map_of (ps_roots p5_state) p5_origin of None \<Rightarrow> (p5_state,1,False)
                | Some p5_root \<Rightarrow> if ps_phase p5_slot = 3 \<and> ps_slot_binding p5_root = p5_binding \<and>
                    ps_slot_epoch p5_root = pf_epoch p5_input \<and> ps_decision_kind p5_root = None \<and>
                    map_of (ps_evidence p5_state) p5_reference = None
                  then ((pf_store_root (p5_root\<lparr>ps_decision_kind := Some Confirmed_Decision,
                        ps_decision_position := Some (ps_revision p5_state)\<rparr>) p5_state)\<lparr>
                        ps_evidence := ps_put p5_reference (p5_binding,Confirmed_Decision) (ps_evidence p5_state)\<rparr>,16,True)
                  else (p5_state,1,False))
           | PF_Credit p5_reference \<Rightarrow>
               (case map_of (ps_roots p5_state) p5_origin of None \<Rightarrow> (p5_state,1,False)
                | Some p5_root \<Rightarrow> if pf_slot_bound p5_binding 0 p5_slot p5_input p5_state \<and> ps_phase p5_slot = 3 \<and>
                    ps_slot_epoch p5_root = pf_epoch p5_input \<and> ps_decision_kind p5_root = Some Confirmed_Decision \<and>
                    map_of (ps_evidence p5_state) p5_reference = Some (p5_binding,Confirmed_Decision) \<and>
                    ps_get (ps_balances p5_state) (ps_holder_account p5_binding (ps_receiver p5_binding)) + p5_amount < 2^64
                  then let p5_account = ps_holder_account p5_binding (ps_receiver p5_binding);
                           p5_credited = (pf_store_reservation (p5_slot\<lparr>ps_phase := 4,ps_pending := 0\<rparr>) p5_state)\<lparr>
                             ps_balances := ps_put p5_account (ps_get (ps_balances p5_state) p5_account + p5_amount) (ps_balances p5_state),
                             ps_funding := ps_put (p5_origin,p5_account) p5_amount (ps_funding p5_state)\<rparr>
                       in (pf_store_root (p5_root\<lparr>ps_settled := Some (ps_revision p5_state)\<rparr>) p5_credited,17,True)
                  else (p5_state,1,False))
           | PF_Reconcile p5_generation p5_reference \<Rightarrow>
               if pf_slot_bound p5_binding p5_generation p5_slot p5_input p5_state \<and> ps_phase p5_slot = 4 \<and>
                  ps_clock p5_state < ps_expires p5_slot \<and>
                  map_of (ps_evidence p5_state) p5_reference = Some (p5_binding,Confirmed_Decision)
               then ((pf_store_reservation (p5_slot\<lparr>ps_phase := 5\<rparr>) p5_state)\<lparr>
                  ps_active := filter (\<lambda>(p5_old,p5_key). p5_old \<noteq> p5_asset) (ps_active p5_state)\<rparr>,18,True)
               else (p5_state,1,False)
           | _ \<Rightarrow> (p5_state,1,False))))"

definition pf_note_step where
  "pf_note_step p5_category p5_sequence p5_code p5_commit p5_waiting p5_state p5_machine =
    p5_machine\<lparr>pf_state := p5_state,pf_trace := pf_trace p5_machine @ [(p5_category,p5_sequence,p5_code,p5_commit,p5_waiting)],
      pf_history := native_resize_read_prefixes (ps_revision p5_state) (pf_snapshot p5_state) (pf_history p5_machine)\<rparr>"

definition pf_ordinary where
  "pf_ordinary p5_verified p5_sequence p5_binding p5_command p5_expected p5_machine =
    (let p5_input = pf_input p5_machine; p5_state = pf_state p5_machine; p5_id = (pf_actor p5_input,p5_sequence) in
      if \<not> p5_verified \<or> ps_asset p5_binding \<noteq> pf_asset p5_input \<or>
         fst (ps_origin p5_binding) \<noteq> pf_source p5_input \<or> ps_destination p5_binding \<noteq> pf_destination p5_input \<or>
         map_of (ps_sessions p5_state) 1 \<noteq> Some (pf_actor p5_input,ps_epoch p5_state)
      then (pf_note_step 1 p5_sequence 1 None False p5_state p5_machine,False)
      else if \<not> ps_up p5_state \<or> \<not> ps_available p5_state
      then (pf_note_step 1 p5_sequence 3 None False p5_state p5_machine,False)
      else if p5_expected \<noteq> ps_cut p5_state
      then (pf_note_step 1 p5_sequence 2 None False p5_state p5_machine,False)
      else if p5_id \<in> set (ps_ordinary_ids p5_state @ ps_legal_ids p5_state @ ps_sync_ids p5_state) \<or>
           map_of (ps_spend_receipts p5_state) p5_id \<noteq> None \<or> Suc (ps_revision p5_state) \<ge> 2^64
      then (pf_note_step 1 p5_sequence 1 None False p5_state p5_machine,False)
      else let (p5_effect,p5_code,p5_committed) = pf_ordinary_body p5_command p5_binding p5_input p5_state;
               p5_commit = (if p5_committed then Some (ps_revision p5_state) else None);
               p5_target = (case p5_command of PF_Credit p5_reference \<Rightarrow> ps_destination p5_binding | _ \<Rightarrow> fst (ps_origin p5_binding));
               p5_final = p5_effect\<lparr>ps_revision := (if p5_committed then Suc (ps_revision p5_state) else ps_revision p5_effect),
                  ps_ordinary_ids := ps_ordinary_ids p5_effect @ [p5_id],
                  ps_journal := ps_journal p5_effect @ (if p5_committed then [(p5_id,p5_target,ps_revision p5_state)] else [])\<rparr>;
               p5_waiting = (p5_code = 17 \<and> (case map_of (ps_roots p5_final) (ps_origin p5_binding) of
                    None \<Rightarrow> True | Some p5_root \<Rightarrow> ps_published p5_root = None \<or>
                       map_of (ps_active p5_final) (ps_asset p5_binding) = Some (ps_origin p5_binding)))
           in (pf_note_step 1 p5_sequence p5_code p5_commit p5_waiting p5_final p5_machine,p5_committed))"

definition pf_freeze where
  "pf_freeze p5_verified p5_receiving p5_sequence p5_expected p5_machine =
    (let p5_input = pf_input p5_machine; p5_state = pf_state p5_machine; p5_binding = pf_freeze_binding p5_input;
         p5_origin = ps_origin p5_binding; p5_id = (pf_actor p5_input,p5_sequence);
         p5_existing = map_of (ps_legal_events p5_state) p5_origin;
         p5_binding_ready = pf_input_domain p5_input \<and> ps_epoch p5_state = pf_epoch p5_input \<and>
           map_of (ps_roots p5_state) p5_origin = None \<and> map_of (ps_reservations p5_state) p5_origin = None;
         p5_transition = map_of (ps_modes p5_state) (pf_source p5_input,pf_asset p5_input) = Some ACTIVE \<and>
           map_of (ps_modes p5_state) (pf_destination p5_input,pf_asset p5_input) = Some ACTIVE;
         p5_prior = (if p5_receiving then (case p5_existing of None \<Rightarrow> False | Some p5_event \<Rightarrow>
             ps_legal_binding p5_event = p5_binding \<and> ps_legal_epoch p5_event = pf_epoch p5_input \<and>
             ps_legal_officer p5_event = pf_actor p5_input \<and> ps_legal_jurisdiction p5_event = pf_jurisdiction p5_input \<and>
             ps_legal_basis_value p5_event = pf_basis p5_input \<and> ps_applied_position p5_event = None)
           else p5_existing = None)
     in if \<not> p5_verified \<or> \<not> ps_up p5_state \<or> \<not> ps_available p5_state \<or>
          map_of (ps_sessions p5_state) 1 \<noteq> Some (pf_actor p5_input,ps_epoch p5_state) \<or>
          p5_expected \<noteq> ps_cut p5_state \<or> \<not> p5_binding_ready \<or> \<not> p5_transition \<or> \<not> p5_prior \<or>
          p5_id \<in> set (ps_ordinary_ids p5_state @ ps_legal_ids p5_state @ ps_sync_ids p5_state) \<or>
          map_of (ps_spend_receipts p5_state) p5_id \<noteq> None \<or> Suc (ps_revision p5_state) \<ge> 2^64
        then (pf_note_step 2 p5_sequence 1 None False p5_state p5_machine,False)
        else let p5_event = (if p5_receiving then the p5_existing else
                 \<lparr>ps_legal_binding = p5_binding,ps_legal_epoch = pf_epoch p5_input,ps_legal_officer = pf_actor p5_input,
                   ps_legal_jurisdiction = pf_jurisdiction p5_input,ps_legal_basis_value = pf_basis p5_input,
                   ps_emitted_position = ps_revision p5_state,ps_applied_position = None,ps_legal_published = None\<rparr>);
                 p5_next_event = (if p5_receiving then p5_event\<lparr>ps_applied_position := Some (ps_revision p5_state)\<rparr> else p5_event);
                 p5_final = p5_state\<lparr>ps_revision := Suc (ps_revision p5_state),
                   ps_legal_events := ps_put p5_origin p5_next_event (ps_legal_events p5_state),
                   ps_modes := (if p5_receiving then map (\<lambda>(p5_key,p5_mode).
                       (p5_key,if snd p5_key = pf_asset p5_input then FROZEN else p5_mode)) (ps_modes p5_state) else ps_modes p5_state),
                   ps_active_freezes := (if p5_receiving then ps_put (pf_asset p5_input) p5_origin (ps_active_freezes p5_state)
                      else ps_active_freezes p5_state),ps_legal_ids := ps_legal_ids p5_state @ [p5_id],
                   ps_journal := ps_journal p5_state @ [(p5_id,if p5_receiving then pf_destination p5_input else pf_source p5_input,ps_revision p5_state)]\<rparr>
             in (pf_note_step 2 p5_sequence (if p5_receiving then 51 else 50) (Some (ps_revision p5_state)) False p5_final p5_machine,True))"

fun pf_commands where
  "pf_commands [] p5_binding p5_sequence p5_machine = Some p5_machine"
| "pf_commands (p5_command # p5_rest) p5_binding p5_sequence p5_machine =
    (let p5_step = pf_ordinary True p5_sequence p5_binding p5_command (ps_cut (pf_state p5_machine)) p5_machine
     in if snd p5_step then pf_commands p5_rest p5_binding (Suc p5_sequence) (fst p5_step) else None)"

definition pf_complete_freeze where
  "pf_complete_freeze p5_machine =
    (let p5_first = pf_freeze True False 10 (ps_cut (pf_state p5_machine)) p5_machine in
     if \<not> snd p5_first then None else
       let p5_second = pf_freeze True True 11 (ps_cut (pf_state (fst p5_first))) (fst p5_first) in
       if \<not> snd p5_second then None else
         pf_commands [PF_Publish] (pf_freeze_binding (pf_input p5_machine)) 12 (fst p5_second))"

definition pf_prepare where
  "pf_prepare p5_source_debit p5_input =
    (if \<not> pf_input_domain p5_input then None else
      let p5_initial = pf_genesis p5_input;
          p5_root = pf_root_binding p5_input;
          p5_prefix = (if p5_source_debit then pf_commands [PF_Reserve 10,PF_Dispatch 0]
                (p5_root\<lparr>ps_root_amount := pf_amount p5_input\<rparr>) 1 p5_initial
             else pf_commands [PF_Reserve 20,PF_Dispatch 0,PF_Debit 0,PF_Record 0,PF_Credit 0,PF_Reconcile 0 0,PF_Publish]
                p5_root 100 p5_initial)
      in case p5_prefix of None \<Rightarrow> None | Some p5_seed \<Rightarrow> pf_complete_freeze p5_seed)"

definition pf_spend_call where
  "pf_spend_call p5_kind p5_machine =
    (let p5_input = pf_input p5_machine; p5_state = pf_state p5_machine; p5_scope = pf_scope p5_input p5_kind;
         p5_order = \<lparr>ps_order_scope = p5_scope,ps_officer = pf_actor p5_input,ps_jurisdiction = pf_jurisdiction p5_input,
           ps_legal_basis = pf_basis p5_input,ps_assets = [pf_asset p5_input],ps_prior_seizure = None,ps_appeal_deadline = None\<rparr>
     in case map_of (ps_roots p5_state) (ps_origin (pf_root_binding p5_input)) of None \<Rightarrow> None
       | Some p5_root \<Rightarrow> case ps_decision_position p5_root of None \<Rightarrow> None | Some p5_reference \<Rightarrow>
         Some \<lparr>ps_route = PS_Force_Inclusion,ps_actor = pf_actor p5_input,ps_call_id = (pf_actor p5_input,1),ps_expected = ps_cut p5_state,
           ps_payload = \<lparr>ps_message = 1,ps_caller = pf_actor p5_input,ps_session = 1,ps_payload_cut = ps_cut p5_state,
             ps_origin_epoch = pf_epoch p5_input,ps_reference = p5_reference,ps_scope = p5_scope\<rparr>,
           ps_enforcement = (if p5_kind = PS_Ordinary then None else Some p5_order)\<rparr>)"

lemma pf_source_protection_is_checked_before_both_ordinary_operations:
  assumes "ps_source_protected p5_binding p5_state"
  shows "pf_ordinary_body (PF_Dispatch p5_generation) p5_binding p5_input p5_state = (p5_state,1,False)"
    "pf_ordinary_body (PF_Debit p5_generation) p5_binding p5_input p5_state = (p5_state,1,False)"
  using assms by (simp_all add: pf_ordinary_body_def Let_def)

lemma pf_direct_checked_cut_failure_does_not_create_an_ordinary_receipt:
  assumes "p5_expected \<noteq> ps_cut (pf_state p5_machine)"
  shows "pf_state (fst (pf_ordinary p5_verified p5_sequence p5_binding p5_command p5_expected p5_machine)) = pf_state p5_machine"
  using assms by (simp add: pf_ordinary_def pf_note_step_def Let_def split: if_splits)

text \<open>
  The seed is computed from genesis through the actual fixture command order.
  Primary operation credentials are the helper's exact holder/generation/epoch,
  session 1, empty version vector and single-asset footprint, with the explicitly
  installed Normal grants. Signature/legal/read callbacks return True exactly
  as this typed fixture does; this is not signed packet validation or legal fact
  truth. Legal grants for Freeze source/receiving and the exact enrollment are
  common bootstrap premises. Each helper names the then-current expected cut.
  Credit's underlying commit and its Waiting collection result are distinct.
  No revision, terminal CommitRef, published Freeze or after-balance is supplied
  by a case outcome. Existing-call replay and other legal operations are outside
  this fresh-prefix producer, while the spend wrapper retains its exact receipt.
\<close>

end
