theory Protected_Spend_G0
  imports "OIP_Protected_Spend_Seed.Protected_Spend_Seed"
begin

datatype pg_operation = PG_Frozen_Read | PG_Ordinary_Spend | PG_Recovery_Spend | PG_Protected_Debit
datatype pg_reply = PG_Current "(product_cut \<times> reg_state option) option"
  | PG_Spend ps_reply | PG_Primary nat "nat option" bool

definition pg_current_mode where
  "pg_current_mode p5_machine =
    (let p5_state = pf_state p5_machine; p5_input = pf_input p5_machine in
      if ps_up p5_state \<and> ps_available p5_state \<and>
         map_of (ps_sessions p5_state) 1 = Some (pf_actor p5_input,ps_epoch p5_state) \<and>
         pf_history p5_machine \<noteq> []
      then Some (ps_cut p5_state,map_of (pf_snapshot_modes (last (pf_history p5_machine)))
           (pf_destination p5_input,pf_asset p5_input)) else None)"

fun pg_spend_code where
  "pg_spend_code PS_Spend_Rejected = (1::nat)"
| "pg_spend_code PS_Spend_Busy = 2"
| "pg_spend_code PS_Spend_Unavailable = 3"
| "pg_spend_code (PS_Spend_Executed p5_origin p5_position) = 30"

fun pg_spend_commit where
  "pg_spend_commit (PS_Spend_Executed p5_origin p5_position) = Some p5_position"
| "pg_spend_commit p5_reply = None"

definition pg_run_prepared where
  "pg_run_prepared p5_require_mode p5_operation p5_machine =
    (let p5_input = pf_input p5_machine; p5_state = pf_state p5_machine in
      case p5_operation of PG_Frozen_Read \<Rightarrow> Some (p5_machine,PG_Current (pg_current_mode p5_machine))
      | PG_Protected_Debit \<Rightarrow>
          let p5_binding = (pf_root_binding p5_input)\<lparr>ps_root_amount := pf_amount p5_input\<rparr>;
              p5_step = pf_ordinary True 3 p5_binding (PF_Debit 0) (ps_cut p5_state) p5_machine;
              p5_after = fst p5_step
          in case last (pf_trace p5_after) of (p5_category,p5_sequence,p5_code,p5_commit,p5_waiting) \<Rightarrow>
               Some (p5_after,PG_Primary p5_code p5_commit p5_waiting)
      | _ \<Rightarrow>
          (case pf_spend_call (if p5_operation = PG_Ordinary_Spend then PS_Ordinary else PS_Recover) p5_machine of
            None \<Rightarrow> None
          | Some p5_call \<Rightarrow> let (p5_after,p5_reply) = ps_submit_spend p5_require_mode True p5_call p5_state in
              Some (pf_note_step 3 1 (pg_spend_code p5_reply) (pg_spend_commit p5_reply) False p5_after p5_machine,PG_Spend p5_reply)))"

definition pg_run where
  "pg_run p5_require_mode p5_operation p5_input =
    (case pf_prepare (p5_operation = PG_Protected_Debit) p5_input of None \<Rightarrow> None
     | Some p5_before \<Rightarrow> map_option (\<lambda>(p5_after,p5_reply). (p5_before,p5_after,p5_reply))
         (pg_run_prepared p5_require_mode p5_operation p5_before))"

definition pg_freeze_ready where
  "pg_freeze_ready p5_machine \<longleftrightarrow>
    (let p5_input = pf_input p5_machine; p5_state = pf_state p5_machine;
         p5_origin = ps_origin (pf_freeze_binding p5_input)
     in map_of (ps_modes p5_state) (pf_source p5_input,pf_asset p5_input) = Some FROZEN \<and>
        map_of (ps_modes p5_state) (pf_destination p5_input,pf_asset p5_input) = Some FROZEN \<and>
        map_of (ps_active_freezes p5_state) (pf_asset p5_input) = Some p5_origin \<and>
        (case map_of (ps_legal_events p5_state) p5_origin of None \<Rightarrow> False | Some p5_event \<Rightarrow>
          ps_legal_binding p5_event = pf_freeze_binding p5_input \<and>
          ps_applied_position p5_event \<noteq> None \<and> ps_legal_published p5_event \<noteq> None) \<and>
        length (pf_history p5_machine) = Suc (ps_revision p5_state) \<and>
        last (pf_history p5_machine) = pf_snapshot p5_state)"

definition pg_spend_ready where
  "pg_spend_ready p5_kind p5_machine \<longleftrightarrow>
    pg_freeze_ready p5_machine \<and>
    (case pf_spend_call p5_kind p5_machine of None \<Rightarrow> False | Some p5_call \<Rightarrow>
       ps_access True p5_call (pf_state p5_machine) \<and>
       ps_expected p5_call = ps_cut (pf_state p5_machine) \<and>
       ps_exact_root (ps_payload p5_call) (pf_state p5_machine) \<and>
       ps_spend_funding (ps_scope (ps_payload p5_call)) (pf_state p5_machine) \<noteq> None)"

theorem pg_accepted_spend_consumes_current_cut_and_retained_exact_root:
  assumes "ps_apply_spend p5_require_mode p5_call p5_state = (p5_after,PS_Spend_Executed p5_origin p5_position)"
  shows "ps_expected p5_call = ps_cut p5_state"
    "ps_payload_cut (ps_payload p5_call) = ps_cut p5_state"
    "ps_exact_root (ps_payload p5_call) p5_state"
    "ps_spend_funding (ps_scope (ps_payload p5_call)) p5_state = Some (p5_after,p5_position)"
    "p5_origin = ps_origin (ps_root (ps_scope (ps_payload p5_call)))"
  using assms by (auto simp: ps_apply_spend_def Let_def split: option.splits if_splits prod.splits)

lemma pg_any_change_to_confirmed_root_reference_refuses:
  assumes "\<not> ps_exact_root (ps_payload p5_call) p5_state"
  shows "snd (ps_apply_spend p5_guard p5_call p5_state) \<noteq> PS_Spend_Executed p5_origin p5_position"
  using assms by (auto simp: ps_apply_spend_def Let_def split: option.splits if_splits prod.splits)

lemma pg_ordinary_mode_mutant_keeps_the_exact_operational_seed:
  "pg_run False p5_operation p5_input =
    (case pf_prepare (p5_operation = PG_Protected_Debit) p5_input of None \<Rightarrow> None
     | Some p5_before \<Rightarrow> map_option (\<lambda>(p5_after,p5_reply). (p5_before,p5_after,p5_reply))
         (pg_run_prepared False p5_operation p5_before))"
  by (simp add: pg_run_def)

lemma pg_mode_removal_cannot_bypass_the_other_source_debit_guard:
  "pg_run_prepared False PG_Protected_Debit p5_machine = pg_run_prepared True PG_Protected_Debit p5_machine"
  by (simp add: pg_run_prepared_def Let_def)

text \<open>
  Four input-only operations are retained. The exact fresh typed producer
  supplies genesis, source-funded root, terminal decision position and completed
  Freeze by executing commands. Read values come from the reached read-history
  prefix and current cut. Mode guard removal is the same prepared Ordinary
  request; it neither supplies an expected verdict nor removes source Debit's
  guard. The conditional acceptance result separates execution from receipt
  retention and the source's actual commit position. Ground readiness and
  positive/negative/mutant values are to be computed in standalone generated
  SML. They are not kernel conclusions injected into the input vectors.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms pg_accepted_spend_consumes_current_cut_and_retained_exact_root
      pg_any_change_to_confirmed_root_reference_refuses pg_ordinary_mode_mutant_keeps_the_exact_operational_seed
      pg_mode_removal_cannot_bypass_the_other_source_debit_guard})
  then () else error "Unexpected oracle in protected spend G0 composition"
\<close>

end
