theory Receiver_State_ABI
  imports "OIP_V062_Receiver_State_Branches.Receiver_State_Branches"
begin

definition rr_publication_words where
  "rr_publication_words published =
    (let origin = binding_key (origin_binding (publication_decision (fst published))) in
     sq_publication_words published @ [fst origin,snd origin])"

fun rr_dispatch_from_words :: "nat list \<Rightarrow> (sw_json_profile \<times> sq_job) option" where
  "rr_dispatch_from_words (deployment # format # authority # target # attempts # status # published) =
    (if format \<ge> 2^32 then None else
       Option.bind (sq_parse_phase status) (\<lambda>phase.
         map_option (\<lambda>pub. ((deployment,format,authority),
           \<lparr>sq_commitment = pub, sq_job_target = target, sq_attempts = attempts, sq_phase = phase\<rparr>))
           (rr_publication_from_words published)))"
| "rr_dispatch_from_words _ = None"

fun rr_result_word where
  "rr_result_word RR_Error = (0 :: nat)"
| "rr_result_word RR_Exact = 1"
| "rr_result_word RR_Changed = 2"

fun rr_plan_rows where
  "rr_plan_rows RR_Refused = [[0]]"
| "rr_plan_rows RR_Already_Recorded = [[1]]"
| "rr_plan_rows (RR_Compare prior_value bytes) = [[2,fst prior_value],snd prior_value,bytes]"

definition rr_race_rows where
  "rr_race_rows profile target prior_value nested outer =
    (let first = snd nested; second = snd outer in
     case (rr_prepare profile target (fst nested) first prior_value,
       rr_prepare profile target (fst outer) second prior_value) of
       (RR_Compare expected_first bytes_first,RR_Compare expected_second bytes_second) \<Rightarrow>
         map_option (\<lambda>stored. [[0],[fst expected_first,fst expected_second],
           snd expected_first,snd expected_second,bytes_first,bytes_second,
           [rr_result_word (rr_finish profile target first RR_Installed None),
            rr_result_word (rr_finish profile target second RR_Compare_Failed (Some bytes_first)),
            rr_result_word (rr_finish profile target second RR_Ambiguous (Some bytes_first)),
            rr_result_word (rr_finish profile target second RR_Compare_Failed (Some (snd prior_value))),
            rr_result_word (rr_finish profile target second RR_Ambiguous None)],
           rr_publication_words stored])
           (rr_readback profile target (sq_key (sq_commitment second)) bytes_first)
       | _ \<Rightarrow> None)"

definition rr_stage_rows where
  "rr_stage_rows profile target prior_value staged job =
    (let key = sq_key (sq_commitment job) in
     Option.bind (rr_readback profile target key (snd prior_value)) (\<lambda>prior.
       map_option (\<lambda>supplied. [[1],[fst prior_value],snd prior_value,staged,
         rr_publication_words prior,rr_publication_words supplied,
         [if sq_key supplied = sq_key prior then 1 else 0,
          if supplied \<noteq> prior then 1 else 0,
          if prior = sq_commitment job then 1 else 0]])
         (rr_readback profile target key staged)))"

definition rr_conflict_rows where
  "rr_conflict_rows profile target prior_value dispatch =
    (let job = snd dispatch in
     map_option (\<lambda>stored. [[2],[fst prior_value],snd prior_value,rr_publication_words stored] @
       rr_plan_rows (rr_prepare profile target (fst dispatch) job prior_value))
       (rr_readback profile target (sq_key (sq_commitment job)) (snd prior_value)))"

fun rr_run_nat :: "nat list list \<Rightarrow> nat list list option" where
  "rr_run_nat ([mode,deployment,format,authority,target,revision] # raw # arguments) =
    (let profile = (deployment,format,authority); prior_value = (revision,raw) in
     if mode = 0 then
       (case arguments of [nested,outer] \<Rightarrow>
          Option.bind (rr_dispatch_from_words nested) (\<lambda>first.
            Option.bind (rr_dispatch_from_words outer) (rr_race_rows profile target prior_value first))
        | _ \<Rightarrow> None)
     else if mode = 1 then
       (case arguments of [authorized,staged] \<Rightarrow>
          Option.bind (rr_dispatch_from_words authorized) (\<lambda>dispatch.
            rr_stage_rows profile target prior_value staged (snd dispatch))
        | _ \<Rightarrow> None)
     else if mode = 2 then
       (case arguments of [authorized] \<Rightarrow>
          Option.bind (rr_dispatch_from_words authorized) (rr_conflict_rows profile target prior_value)
        | _ \<Rightarrow> None)
     else None)"
| "rr_run_nat _ = None"

definition rr_run_integer :: "integer list list \<Rightarrow> integer list list option" where
  "rr_run_integer rows =
    (if list_all (list_all (\<lambda>word. 0 \<le> word \<and> word < 2^64)) rows then
       map_option (map (map integer_of_nat)) (rr_run_nat (map (map nat_of_integer) rows))
     else None)"

lemma rr_refused_conflict_abi_keeps_the_before_bytes:
  assumes "rr_readback profile target (sq_key (sq_commitment (snd dispatch))) (snd prior_value) = Some stored"
    "rr_prepare profile target (fst dispatch) (snd dispatch) prior_value = RR_Refused"
  shows "rr_conflict_rows profile target prior_value dispatch =
    Some [[2],[fst prior_value],snd prior_value,rr_publication_words stored,[0]]"
  using assms by (simp add: rr_conflict_rows_def Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms rr_refused_conflict_abi_keeps_the_before_bytes})
  then () else error "Unexpected oracle in receiver journal ABI"
\<close>

export_code rr_run_integer in SML module_name Receiver_Journal_ABI file_prefix "receiver_journal_abi"

end
