theory Wire_Code_Finite_Source_Slice
  imports Wire_Code_Finite_Raw_Ordinary
begin

record code_finite_source_slice =
  slice_financial :: code_finite_reservation_machine
  slice_source_bindings :: "(source_key \<times> code_source_binding) list"
  slice_holder_balances :: "((source_account \<times> nat) \<times> nat) list"
  slice_revision :: nat
  slice_binding_epoch :: nat
  slice_separator :: nat

datatype code_finite_source_decision =
    Code_Finite_Source_Validation wire_refusal
  | Code_Finite_Source_Pending
  | Code_Finite_Source_Decided code_source_call_payload code_source_outcome

definition code_finite_plain_rejection :: code_source_outcome where
  "code_finite_plain_rejection = \<lparr>source_outcome_reply = Code_Source_Outcome_Rejected,source_outcome_commit = None\<rparr>"

fun code_finite_outcome_at :: "nat \<Rightarrow> reservation_reply \<Rightarrow> code_source_outcome option" where
  "code_finite_outcome_at position Request_Rejected = Some code_finite_plain_rejection"
| "code_finite_outcome_at position Reservation_Busy =
    Some \<lparr>source_outcome_reply = Code_Source_Outcome_Busy,source_outcome_commit = None\<rparr>"
| "code_finite_outcome_at position Reservation_Acquired =
    Some \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Reserved_Reply,source_outcome_commit = Some position\<rparr>"
| "code_finite_outcome_at position Source_Dispatched =
    Some \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Dispatched_Reply,source_outcome_commit = Some position\<rparr>"
| "code_finite_outcome_at position Source_Debited =
    Some \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Debited_Reply,source_outcome_commit = Some position\<rparr>"
| "code_finite_outcome_at position reply = None"

definition code_finite_slice_credential :: "code_finite_lock_context \<Rightarrow> code_finite_source_slice \<Rightarrow>
  code_finite_selected_ordinary \<Rightarrow> bool" where
  "code_finite_slice_credential descriptor state chosen =
    (let payload = finite_selected_payload chosen; binding = source_payload_binding payload;
         current = map_of (finite_reservations (finite_machine_state (slice_financial state))) (source_binding_origin binding)
     in case finite_selected_command chosen of Code_Finite_Reserve duration \<Rightarrow> source_payload_credential payload = None
      | command \<Rightarrow>
        (case (source_payload_credential payload,map_of (slice_source_bindings state) (source_binding_origin binding),current) of
          (Some credential,Some stored_binding,Some stored) \<Rightarrow>
            let token = credential_token credential;
                generation = (case command of Code_Finite_Dispatch selected \<Rightarrow> selected
                  | Code_Finite_Debit selected \<Rightarrow> selected | Code_Finite_Reserve duration \<Rightarrow> 0)
            in stored_binding = binding \<and> token_asset token = source_binding_asset binding \<and>
               credential_origin credential = source_binding_origin binding \<and>
               token_owner token = reservation_worker stored \<and> reservation_worker stored = source_payload_caller payload \<and>
               token_generation token = reservation_generation stored \<and> generation = reservation_generation stored \<and>
               credential_epoch credential = finite_context_authority_epoch descriptor
        | _ \<Rightarrow> False))"

definition code_finite_slice_payer :: "code_finite_source_slice \<Rightarrow> code_finite_selected_ordinary \<Rightarrow> bool" where
  "code_finite_slice_payer state chosen =
    (case finite_selected_command chosen of Code_Finite_Reserve duration \<Rightarrow> True
     | _ \<Rightarrow> let binding = source_payload_binding (finite_selected_payload chosen);
         key = ((fst (source_binding_origin binding),source_binding_asset binding),source_binding_owner binding)
       in source_binding_amount binding \<le> code_finite_nat_default (slice_holder_balances state) key)"

definition code_finite_publish_financial_slice :: "code_finite_source_slice \<Rightarrow> code_finite_selected_ordinary \<Rightarrow>
  code_finite_reservation_machine \<Rightarrow> reservation_reply \<Rightarrow> code_source_outcome \<Rightarrow> code_finite_source_slice" where
  "code_finite_publish_financial_slice state chosen financial_after reply outcome =
    (let binding = source_payload_binding (finite_selected_payload chosen);
         key = ((fst (source_binding_origin binding),source_binding_asset binding),source_binding_owner binding)
     in state\<lparr>slice_financial := financial_after,
       slice_source_bindings := (if reply = Reservation_Acquired then
         code_finite_put (source_binding_origin binding) binding (slice_source_bindings state) else slice_source_bindings state),
       slice_holder_balances := (if reply = Source_Debited then code_finite_put key
         (code_finite_nat_default (slice_holder_balances state) key - source_binding_amount binding) (slice_holder_balances state)
         else slice_holder_balances state),
       slice_revision := (if source_outcome_commit outcome = None then slice_revision state else Suc (slice_revision state))\<rparr>)"

definition code_finite_run_source_slice :: "nat \<Rightarrow> code_finite_lock_context \<Rightarrow> wire_bytes \<Rightarrow>
  code_finite_source_slice \<Rightarrow> (code_finite_source_slice \<times> code_finite_source_decision)" where
  "code_finite_run_source_slice frame_limit descriptor bytes state =
    (case code_finite_select_raw_ordinary frame_limit descriptor (slice_binding_epoch state) (slice_separator state) bytes of
       Code_Finite_Raw_Refused reason \<Rightarrow> (state,Code_Finite_Source_Validation reason)
     | Code_Finite_Raw_Pending \<Rightarrow> (state,Code_Finite_Source_Pending)
     | Code_Finite_Raw_Selected chosen \<Rightarrow>
       if \<not> code_finite_slice_credential descriptor state chosen \<or> \<not> code_finite_slice_payer state chosen
       then (state,Code_Finite_Source_Decided (finite_selected_payload chosen) code_finite_plain_rejection)
       else let (financial_after,reply) = code_finite_closed_command descriptor (finite_selected_request chosen)
              (finite_selected_versions chosen) (finite_selected_command chosen) (slice_financial state)
         in case code_finite_outcome_at (slice_revision state) reply of None \<Rightarrow> (state,Code_Finite_Source_Pending)
          | Some outcome \<Rightarrow> (code_finite_publish_financial_slice state chosen financial_after reply outcome,
              Code_Finite_Source_Decided (finite_selected_payload chosen) outcome))"

lemma an_unbound_generation_or_source_owner_cannot_reach_the_finite_financial_consumer:
  assumes selected: "code_finite_select_raw_ordinary frame_limit descriptor (slice_binding_epoch state) (slice_separator state) bytes =
      Code_Finite_Raw_Selected chosen"
    and refused: "\<not> code_finite_slice_credential descriptor state chosen \<or> \<not> code_finite_slice_payer state chosen"
  shows "code_finite_run_source_slice frame_limit descriptor bytes state =
    (state,Code_Finite_Source_Decided (finite_selected_payload chosen) code_finite_plain_rejection)"
  using selected refused by (simp add: code_finite_run_source_slice_def)

lemma each_finite_slice_outcome_keeps_its_program_produced_position:
  assumes "code_finite_outcome_at revision reply = Some outcome"
    "source_outcome_commit outcome = Some position"
  shows "position = revision"
  using assms by (cases reply) (auto simp: code_finite_plain_rejection_def)

lemma a_finite_slice_outcome_has_exactly_the_existing_source_recorded_kind_and_commit_rule:
  assumes "code_finite_outcome_at revision reply = Some outcome"
  shows "code_source_outcome_commit_matches outcome"
  using assms by (cases reply)
    (auto simp: code_source_outcome_commit_matches_def code_finite_plain_rejection_def)

lemma the_finite_source_revision_is_not_set_from_an_observed_after_state:
  "slice_revision (code_finite_publish_financial_slice state chosen financial_after reply outcome) =
    (if source_outcome_commit outcome = None then slice_revision state else Suc (slice_revision state))"
  by (simp add: code_finite_publish_financial_slice_def Let_def)

theorem a_committed_source_slice_uses_the_selected_fixed_financial_operation:
  assumes run: "code_finite_run_source_slice frame_limit descriptor bytes before = (after,Code_Finite_Source_Decided payload outcome)"
    and commit: "source_outcome_commit outcome = Some position"
  obtains chosen :: code_finite_selected_ordinary and financial_after :: code_finite_reservation_machine and reply :: reservation_reply
  where "code_finite_select_raw_ordinary frame_limit descriptor (slice_binding_epoch before) (slice_separator before) bytes =
      Code_Finite_Raw_Selected chosen"
    "code_finite_slice_credential descriptor before chosen" "code_finite_slice_payer before chosen"
    "code_finite_closed_command descriptor (finite_selected_request chosen) (finite_selected_versions chosen)
       (finite_selected_command chosen) (slice_financial before) = (financial_after,reply)"
    "code_finite_outcome_at (slice_revision before) reply = Some outcome"
    "payload = finite_selected_payload chosen"
    "after = code_finite_publish_financial_slice before chosen financial_after reply outcome"
    "position = slice_revision before"
proof -
  let ?selection = "code_finite_select_raw_ordinary frame_limit descriptor (slice_binding_epoch before) (slice_separator before) bytes"
  obtain chosen
    where selected: "?selection = Code_Finite_Raw_Selected chosen"
  proof (cases ?selection)
    case (Code_Finite_Raw_Refused reason)
    with run show thesis by (simp add: code_finite_run_source_slice_def)
  next
    case Code_Finite_Raw_Pending
    with run show thesis by (simp add: code_finite_run_source_slice_def)
  next
    case (Code_Finite_Raw_Selected chosen)
    show thesis by (rule that[OF Code_Finite_Raw_Selected])
  qed
  have allowed: "code_finite_slice_credential descriptor before chosen \<and> code_finite_slice_payer before chosen"
  proof (rule ccontr)
    assume "\<not> (code_finite_slice_credential descriptor before chosen \<and> code_finite_slice_payer before chosen)"
    then have denied: "\<not> code_finite_slice_credential descriptor before chosen \<or> \<not> code_finite_slice_payer before chosen" by auto
    have rejected: "code_finite_run_source_slice frame_limit descriptor bytes before =
      (before,Code_Finite_Source_Decided (finite_selected_payload chosen) code_finite_plain_rejection)"
      using selected denied by (simp add: code_finite_run_source_slice_def)
    have outcome: "outcome = code_finite_plain_rejection" using run rejected by auto
    show False using commit outcome by (simp add: code_finite_plain_rejection_def)
  qed
  have credential: "code_finite_slice_credential descriptor before chosen"
    and payer: "code_finite_slice_payer before chosen" using allowed by auto
  obtain financial_after reply
    where executed: "code_finite_closed_command descriptor (finite_selected_request chosen) (finite_selected_versions chosen)
      (finite_selected_command chosen) (slice_financial before) = (financial_after,reply)"
    by (cases "code_finite_closed_command descriptor (finite_selected_request chosen) (finite_selected_versions chosen)
      (finite_selected_command chosen) (slice_financial before)") auto
  have computed: "code_finite_outcome_at (slice_revision before) reply = Some outcome"
  proof (cases "code_finite_outcome_at (slice_revision before) reply")
    case None
    with run selected credential payer executed show ?thesis by (simp add: code_finite_run_source_slice_def Let_def)
  next
    case (Some candidate)
    have reduced: "code_finite_run_source_slice frame_limit descriptor bytes before =
      (code_finite_publish_financial_slice before chosen financial_after reply candidate,
        Code_Finite_Source_Decided (finite_selected_payload chosen) candidate)"
      by (simp add: code_finite_run_source_slice_def selected credential payer executed Some Let_def)
    have same: "candidate = outcome" using run reduced by auto
    show ?thesis using Some same by simp
  qed
  have reduced: "code_finite_run_source_slice frame_limit descriptor bytes before =
      (code_finite_publish_financial_slice before chosen financial_after reply outcome,
        Code_Finite_Source_Decided (finite_selected_payload chosen) outcome)"
    by (simp add: code_finite_run_source_slice_def selected credential payer executed computed Let_def)
  have payload: "payload = finite_selected_payload chosen"
    and after: "after = code_finite_publish_financial_slice before chosen financial_after reply outcome"
    using run reduced by auto
  have position: "position = slice_revision before"
    by (rule each_finite_slice_outcome_keeps_its_program_produced_position[OF computed commit])
  show thesis by (rule that[OF selected credential payer executed computed payload after position])
qed

text \<open>
  This is the source credential/exact-payer extension around the proved
  closed financial representation. Binding.owner is retained separately
  from the old binding, and commit annotations are produced from this
  program's own pre-step ledger revision. Unsupported old replies such as
  Source_Already_Debited remain Pending; they are not mapped to invented
  source acceptance. Full admission/current grants/availability/fresh-cut/
  retained-result ordering, origin policy, original resolver and response
  production must surround this slice. This is not the complete authority.
  In a real source call, store_result/result access and reply transport use
  these exact payload/outcome values only after that further composition.
\<close>

end
