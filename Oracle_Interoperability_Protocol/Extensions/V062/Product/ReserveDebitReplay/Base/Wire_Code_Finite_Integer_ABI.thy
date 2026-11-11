theory Wire_Code_Finite_Integer_ABI
  imports Wire_Code_Finite_Source_Slice "OIP_Message_Code.Wire_Code_Oracle_Contract"
begin

record code_finite_integer_runner =
  integer_runner_context :: code_finite_lock_context
  integer_runner_slice :: code_finite_source_slice
  integer_runner_source :: source_account
  integer_runner_owner :: nat
  integer_runner_last_origin :: "source_key option"

definition code_finite_single_asset_seed :: "integer list \<Rightarrow> integer list \<Rightarrow> code_finite_integer_runner option" where
  "code_finite_single_asset_seed metadata actors =
    (if length metadata \<noteq> 9 \<or> \<not> code_integer_u64_values (metadata @ actors) then None
     else let values = map nat_of_integer metadata; callers = map nat_of_integer actors;
          origin = values ! 0; receiver = values ! 1; asset = values ! 2; owner = values ! 3;
          balance = values ! 4; epoch = values ! 5; relay = values ! 6; version = values ! 7; separator = values ! 8;
          descriptor = \<lparr>finite_context_endpoint = origin,finite_context_relay_epoch = relay,
            finite_context_authority_epoch = epoch,finite_context_version = version,
            finite_context_permissions = map (\<lambda>who. Code_Finite_Asset_Binding who asset) callers,
            finite_context_readers = callers,
            finite_context_metadata = [((origin,asset),\<lparr>as_reg_state = ACTIVE\<rparr>),((receiver,asset),\<lparr>as_reg_state = ACTIVE\<rparr>)],
            finite_context_metadata_locks = [],finite_context_restriction_clear = [asset],finite_context_dependencies = [],
            finite_context_write_permissions = [],finite_context_spend_permissions = []\<rparr>;
          financial = \<lparr>finite_machine_state = \<lparr>finite_asset_owners = [],finite_reservations = [],
            finite_asset_values = [(asset,0)],finite_asset_versions = [(asset,0)],finite_source_units = [((origin,asset),balance)],
            finite_destination_units = [],finite_funded_units = [],finite_source_effects = [],finite_issued_certificates = [],
            finite_consumed_at = [],finite_credit_history = [],finite_descendants = [],finite_clock = 0\<rparr>,
            finite_machine_journal = [],finite_machine_observations = []\<rparr>;
          slice = \<lparr>slice_financial = financial,slice_source_bindings = [],slice_holder_balances = [(((origin,asset),owner),balance)],
            slice_revision = 0,slice_binding_epoch = epoch,slice_separator = separator\<rparr>
      in Some \<lparr>integer_runner_context = descriptor,integer_runner_slice = slice,integer_runner_source = (origin,asset),
           integer_runner_owner = owner,integer_runner_last_origin = None\<rparr>)"

fun code_finite_phase_integer :: "reservation_phase option \<Rightarrow> integer" where
  "code_finite_phase_integer None = 0"
| "code_finite_phase_integer (Some Reservation_Held) = 1"
| "code_finite_phase_integer (Some Source_Submitted) = 2"
| "code_finite_phase_integer (Some Source_Pending) = 3"
| "code_finite_phase_integer (Some Source_Confirmed) = 4"
| "code_finite_phase_integer (Some Source_Returned) = 5"
| "code_finite_phase_integer (Some Source_Cancelled) = 6"

definition code_finite_runner_integer_view :: "code_finite_integer_runner \<Rightarrow> integer list" where
  "code_finite_runner_integer_view runner =
    (let slice = integer_runner_slice runner; financial = finite_machine_state (slice_financial slice);
         phase = Option.bind (integer_runner_last_origin runner) (\<lambda>key. map_option reservation_phase (map_of (finite_reservations financial) key))
     in [integer_of_nat (slice_revision slice),
         integer_of_nat (code_finite_nat_default (finite_source_units financial) (integer_runner_source runner)),
         integer_of_nat (code_finite_nat_default (slice_holder_balances slice) (integer_runner_source runner,integer_runner_owner runner)),
         integer_of_nat (sum_list (map binding_amount (finite_source_effects financial))),code_finite_phase_integer phase,
         integer_of_nat (length (finite_machine_journal (slice_financial slice))),
         integer_of_nat (length (slice_source_bindings slice))])"

fun code_finite_integer_decision :: "code_finite_source_decision \<Rightarrow> integer list" where
  "code_finite_integer_decision Code_Finite_Source_Pending = [-1,-1,0,0]"
| "code_finite_integer_decision (Code_Finite_Source_Validation reason) = [1,integer_of_nat (code_transport_refusal_number reason),0,0]"
| "code_finite_integer_decision (Code_Finite_Source_Decided payload outcome) =
    [0,integer_of_nat (code_source_ordinary_number (source_outcome_reply outcome)),
      (case source_outcome_commit outcome of None \<Rightarrow> 0 | Some position \<Rightarrow> 1),
      (case source_outcome_commit outcome of None \<Rightarrow> 0 | Some position \<Rightarrow> integer_of_nat position)]"

definition code_finite_raw_integer_step :: "integer list \<Rightarrow> code_finite_integer_runner \<Rightarrow>
  (code_finite_integer_runner \<times> integer list)" where
  "code_finite_raw_integer_step bytes runner =
    (if \<not> code_integer_octet_values bytes then (runner,[-2,-1,0,0] @ code_finite_runner_integer_view runner)
     else let (slice_after,decision) = code_finite_run_source_slice 1048576 (integer_runner_context runner)
            (map nat_of_integer bytes) (integer_runner_slice runner);
          origin = (case decision of Code_Finite_Source_Decided payload outcome \<Rightarrow> Some (source_binding_origin (source_payload_binding payload))
            | _ \<Rightarrow> integer_runner_last_origin runner);
          after = runner\<lparr>integer_runner_slice := slice_after,integer_runner_last_origin := origin\<rparr>
      in (after,code_finite_integer_decision decision @ code_finite_runner_integer_view after))"

lemma invalid_finite_seed_metadata_cannot_create_an_opaque_runner:
  assumes "length metadata \<noteq> 9 \<or> \<not> code_integer_u64_values (metadata @ actors)"
  shows "code_finite_single_asset_seed metadata actors = None"
  using assms by (simp add: code_finite_single_asset_seed_def)

lemma invalid_integer_octets_cannot_change_the_finite_runner:
  assumes "\<not> code_integer_octet_values bytes"
  shows "fst (code_finite_raw_integer_step bytes runner) = runner"
  using assms by (simp add: code_finite_raw_integer_step_def)

theorem an_in_domain_integer_step_calls_only_the_fixed_raw_model_operation:
  assumes domain: "code_integer_octet_values bytes"
  shows "code_finite_raw_integer_step bytes runner =
    (let (slice_after,decision) = code_finite_run_source_slice 1048576 (integer_runner_context runner)
         (map nat_of_integer bytes) (integer_runner_slice runner);
         origin = (case decision of Code_Finite_Source_Decided payload outcome \<Rightarrow> Some (source_binding_origin (source_payload_binding payload))
           | _ \<Rightarrow> integer_runner_last_origin runner);
         after = runner\<lparr>integer_runner_slice := slice_after,integer_runner_last_origin := origin\<rparr>
      in (after,code_finite_integer_decision decision @ code_finite_runner_integer_view after))"
  using domain by (simp add: code_finite_raw_integer_step_def)

lemma integer_decision_keeps_the_model_outcome_code_and_commit:
  "code_finite_integer_decision (Code_Finite_Source_Decided payload outcome) ! 1 =
    integer_of_nat (code_source_ordinary_number (source_outcome_reply outcome))"
  "code_finite_integer_decision (Code_Finite_Source_Decided payload outcome) ! 2 =
    (if source_outcome_commit outcome = None then 0 else 1)"
  by (simp_all split: option.splits)

text \<open>
  This development ABI exposes only integer lists and an opaque runner.
  Generated SML datatype constructors/signatures are not edited. The seed
  domain is a single ACTIVE asset, no prior allocation/dependency/reservation,
  the provided source owner/balance/epoch and explicit model coordinates.
  Metadata order is origin,receiver,asset,owner,balance,epoch,relay,version,
  separator; actors are a separate finite u64 list. It is not a generic
  genesis deserializer. Raw bytes are decoded by the model before choosing
  Reserve/Dispatch/Debit. Output prefix is status,code,hasCommit,commit,
  followed by revision,pool,payer,pending,phase,journalLength,bindingCount.
  It remains a financial slice: current auth/grants/retained retry/resolver/
  signed response and permanent full reference CI are separate work.
\<close>

end
