theory IBC_Transfer_Evidence
  imports "Promotion_Resolution"
begin

section \<open>ICS-004 destination proof and receive boundary\<close>

type_synonym ibc_height = "nat \<times> nat"

datatype ibc_order = IBC_Unordered | IBC_Ordered | IBC_Ordered_Allow_Timeout
datatype ibc_send_mode = IBC_Escrowed | IBC_Burned
datatype ibc_ack = IBC_Ack_Success | IBC_Ack_Error
datatype ibc_receipt = IBC_Packet_Receipt | IBC_Timeout_Receipt
datatype ibc_timeout_profile = ICS004_Text | IBC_Go_10

record ibc_packet =
  ibc_source_chain :: nat
  ibc_source_port :: nat
  ibc_source_channel :: nat
  ibc_destination_chain :: nat
  ibc_destination_port :: nat
  ibc_destination_channel :: nat
  ibc_sequence :: nat
  ibc_denom :: nat
  ibc_sender :: nat
  ibc_receiver :: nat
  ibc_amount :: nat
  ibc_memo :: "nat list"
  ibc_send_mode :: ibc_send_mode
  ibc_timeout_height :: "ibc_height option"
  ibc_timeout_time :: "nat option"

definition ibc_height_le :: "ibc_height \<Rightarrow> ibc_height \<Rightarrow> bool" where
  "ibc_height_le first second \<longleftrightarrow>
    fst first < fst second \<or> (fst first = fst second \<and> snd first \<le> snd second)"

lemma ibc_height_le_trans:
  assumes first: "ibc_height_le a b" and second: "ibc_height_le b c"
  shows "ibc_height_le a c"
proof -
  have ab: "fst a \<le> fst b" and bc: "fst b \<le> fst c"
    using first second by (auto simp: ibc_height_le_def intro: less_imp_le)
  have ac: "fst a \<le> fst c" by (rule order_trans[OF ab bc])
  show ?thesis
  proof (cases "fst a = fst c")
    case False
    have "fst a < fst c" using ac False by simp
    then show ?thesis by (simp add: ibc_height_le_def)
  next
    case True
    have mid: "fst a = fst b" using ab bc True by (auto intro: antisym)
    have ab_minor: "snd a \<le> snd b" and bc_minor: "snd b \<le> snd c"
      using first second True mid by (simp_all add: ibc_height_le_def)
    have "snd a \<le> snd c" by (rule order_trans[OF ab_minor bc_minor])
    with True show ?thesis by (simp add: ibc_height_le_def)
  qed
qed

definition ibc_elapsed where
  "ibc_elapsed packet height time \<longleftrightarrow>
    (\<exists>limit. ibc_timeout_height packet = Some limit \<and> ibc_height_le limit height) \<or>
    (\<exists>limit. ibc_timeout_time packet = Some limit \<and> limit \<le> time)"

lemma ibc_elapsed_is_monotone:
  assumes "ibc_elapsed packet earlier_height earlier_time"
    "ibc_height_le earlier_height later_height" "earlier_time \<le> later_time"
  shows "ibc_elapsed packet later_height later_time"
  using assms by (auto simp: ibc_elapsed_def dest: ibc_height_le_trans order_trans)

definition ibc_deadline_fields_valid where
  "ibc_deadline_fields_valid packet \<longleftrightarrow>
    (ibc_timeout_height packet \<noteq> None \<or> ibc_timeout_time packet \<noteq> None) \<and>
    (\<forall>limit. ibc_timeout_height packet = Some limit \<longrightarrow> 0 < snd limit) \<and>
    (\<forall>limit. ibc_timeout_time packet = Some limit \<longrightarrow> 0 < limit)"

record ibc_proven_destination =
  ibc_proof_height :: ibc_height
  ibc_proof_time :: nat
  ibc_reported_next :: "nat option"
  ibc_proof_next :: "nat option"
  ibc_proof_receipt :: "ibc_receipt option option"
  ibc_proof_closed :: bool

datatype ibc_terminal_evidence =
    IBC_Acknowledgement ibc_packet ibc_ack
  | IBC_Elapsed_Proof ibc_packet ibc_proven_destination
  | IBC_Closed_Proof ibc_packet ibc_proven_destination

definition ibc_absent_for_elapsed where
  "ibc_absent_for_elapsed profile order packet facts \<longleftrightarrow>
    (case order of IBC_Unordered \<Rightarrow> ibc_proof_receipt facts = Some None
     | IBC_Ordered \<Rightarrow> (\<exists>next. ibc_proof_next facts = Some next \<and>
        (if profile = ICS004_Text then next = ibc_sequence packet else next \<le> ibc_sequence packet))
     | IBC_Ordered_Allow_Timeout \<Rightarrow> profile = ICS004_Text \<and>
        ibc_reported_next facts = Some (Suc (ibc_sequence packet)) \<and>
        ibc_proof_receipt facts = Some (Some IBC_Timeout_Receipt))"

definition ibc_absent_for_close where
  "ibc_absent_for_close profile order packet facts \<longleftrightarrow>
    (case order of IBC_Unordered \<Rightarrow> ibc_proof_receipt facts = Some None
     | IBC_Ordered \<Rightarrow> (\<exists>next. ibc_proof_next facts = Some next \<and> next \<le> ibc_sequence packet)
     | IBC_Ordered_Allow_Timeout \<Rightarrow> profile = ICS004_Text \<and>
        (\<exists>next. ibc_reported_next facts = Some next \<and>
          (if ibc_sequence packet < next then ibc_proof_receipt facts = Some (Some IBC_Timeout_Receipt)
           else ibc_proof_next facts = Some next)))"

fun ibc_evidence_kind where
  "ibc_evidence_kind profile order (IBC_Acknowledgement packet ack) =
    Some (packet, if ack = IBC_Ack_Success then Resolve_Credit else Resolve_Return)"
| "ibc_evidence_kind profile order (IBC_Elapsed_Proof packet facts) =
    (if ibc_elapsed packet (ibc_proof_height facts) (ibc_proof_time facts) \<and>
        ibc_absent_for_elapsed profile order packet facts then Some (packet, Resolve_Return) else None)"
| "ibc_evidence_kind profile order (IBC_Closed_Proof packet facts) =
    (if ibc_proof_closed facts \<and> ibc_absent_for_close profile order packet facts
     then Some (packet, Resolve_Return) else None)"

record ibc_receiver_state =
  ibc_receiver_open :: bool
  ibc_receiver_height :: ibc_height
  ibc_receiver_time :: nat
  ibc_receiver_first :: nat
  ibc_receiver_next :: nat
  ibc_receiver_receipts :: "nat \<Rightarrow> ibc_receipt option"

datatype ibc_receive_outcome =
    IBC_Receive_Refused | IBC_Forward_Application | IBC_Marked_Timeout | IBC_Early_OAT_Return

definition ibc_sequence_is_fresh where
  "ibc_sequence_is_fresh order packet receiver \<longleftrightarrow>
    ibc_receiver_first receiver \<le> ibc_sequence packet \<and>
    (if order = IBC_Unordered then ibc_receiver_receipts receiver (ibc_sequence packet) = None
     else ibc_receiver_next receiver = ibc_sequence packet)"

definition ibc_receive where
  "ibc_receive order commitment_verified packet receiver =
    (if \<not> commitment_verified \<or> \<not> ibc_receiver_open receiver \<or> \<not> ibc_sequence_is_fresh order packet receiver
     then (receiver, IBC_Receive_Refused)
     else if ibc_elapsed packet (ibc_receiver_height receiver) (ibc_receiver_time receiver) then
       if order = IBC_Ordered_Allow_Timeout then
         (receiver\<lparr>ibc_receiver_next := Suc (ibc_receiver_next receiver),
           ibc_receiver_receipts := (ibc_receiver_receipts receiver)(ibc_sequence packet := Some IBC_Timeout_Receipt)\<rparr>,
           IBC_Marked_Timeout)
       else (receiver, IBC_Receive_Refused)
     else case order of
       IBC_Unordered \<Rightarrow> (receiver\<lparr>ibc_receiver_receipts :=
         (ibc_receiver_receipts receiver)(ibc_sequence packet := Some IBC_Packet_Receipt)\<rparr>, IBC_Forward_Application)
     | IBC_Ordered \<Rightarrow> (receiver\<lparr>ibc_receiver_next := Suc (ibc_receiver_next receiver)\<rparr>, IBC_Forward_Application)
     | IBC_Ordered_Allow_Timeout \<Rightarrow> (receiver, IBC_Early_OAT_Return))"

lemma proven_deadline_rules_out_later_delivery:
  assumes "ibc_elapsed packet proof_height proof_time"
    "ibc_height_le proof_height (ibc_receiver_height receiver)" "proof_time \<le> ibc_receiver_time receiver"
  shows "snd (ibc_receive order commitment_verified packet receiver) \<noteq> IBC_Forward_Application"
  using ibc_elapsed_is_monotone[OF assms] by (simp add: ibc_receive_def)

lemma a_closed_destination_does_not_deliver:
  "\<not> ibc_receiver_open receiver \<Longrightarrow>
    ibc_receive order commitment_verified packet receiver = (receiver, IBC_Receive_Refused)"
  by (simp add: ibc_receive_def)

lemma live_oat_timeout_writes_the_exact_destination_marker:
  assumes "ibc_receiver_open receiver" "ibc_sequence_is_fresh IBC_Ordered_Allow_Timeout packet receiver"
    "ibc_elapsed packet (ibc_receiver_height receiver) (ibc_receiver_time receiver)"
  shows "let (after, outcome) = ibc_receive IBC_Ordered_Allow_Timeout True packet receiver in
    outcome = IBC_Marked_Timeout \<and> ibc_receiver_next after = Suc (ibc_sequence packet) \<and>
    ibc_receiver_receipts after (ibc_sequence packet) = Some IBC_Timeout_Receipt"
  using assms by (simp add: ibc_receive_def ibc_sequence_is_fresh_def)

lemma the_pinned_oat_receive_returns_before_the_early_application_path:
  assumes "ibc_receiver_open receiver" "ibc_sequence_is_fresh IBC_Ordered_Allow_Timeout packet receiver"
    "\<not> ibc_elapsed packet (ibc_receiver_height receiver) (ibc_receiver_time receiver)"
  shows "ibc_receive IBC_Ordered_Allow_Timeout True packet receiver = (receiver, IBC_Early_OAT_Return)"
  using assms by (simp add: ibc_receive_def)

lemma a_go10_timeout_has_no_ordered_allow_timeout_profile:
  "ibc_evidence_kind IBC_Go_10 IBC_Ordered_Allow_Timeout (IBC_Elapsed_Proof packet facts) = None"
  "ibc_evidence_kind IBC_Go_10 IBC_Ordered_Allow_Timeout (IBC_Closed_Proof packet facts) = None"
  by (simp_all add: ibc_absent_for_elapsed_def ibc_absent_for_close_def)

end
