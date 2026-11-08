theory Legal_Admission
  imports Read_Program
begin

datatype regulatory_entry = Regulatory_Normal | Regulatory_Administrative | Regulatory_Adapter | Regulatory_Force_Inclusion
datatype legal_stage = Legal_Source_Emission | Legal_Receiving_Commit

datatype legal_refusal =
    Invalid_Legal_Authority
  | Invalid_Legal_State
  | Missing_Prior_Freeze
  | Missing_Prior_Seizure
  | Appeal_Deadline_Mismatch
  | Appeal_Still_Open
  | Missing_Confiscation_Destination
  | Conflicting_Legal_Order
  | Invalid_Legal_Binding

datatype legal_admission = Legal_Admit | Legal_Refuse legal_refusal

record product_legal_order =
  legal_origin :: source_key
  legal_binding :: transfer_binding
  legal_asset :: product_asset
  legal_action :: reg_action
  legal_officer :: product_principal
  legal_jurisdiction :: nat
  legal_basis :: nat
  legal_scope :: "product_asset set"
  legal_issuance_epoch :: nat
  legal_predecessor :: "source_key option"
  legal_appeal_deadline :: "nat option"
  legal_destination :: "nat option"

record product_legal_event =
  applied_order :: product_legal_order
  applied_legal_cut :: product_cut

record legal_product_world =
  legal_reads :: product_read_world
  issued_legal_orders :: "source_key \<Rightarrow> product_legal_order option"
  committed_legal_events :: "source_key \<Rightarrow> product_legal_event option"
  active_freeze_event :: "product_asset \<Rightarrow> source_key option"
  active_seizure_event :: "product_asset \<Rightarrow> source_key option"

definition initial_legal_world where
  "initial_legal_world s = \<lparr>legal_reads = s, issued_legal_orders = (\<lambda>_. None),
    committed_legal_events = (\<lambda>_. None), active_freeze_event = (\<lambda>_. None), active_seizure_event = (\<lambda>_. None)\<rparr>"

definition legal_current_core where
  "legal_current_core s = authoritative_read_core (read_authority (legal_reads s))"

definition legal_current_cut where
  "legal_current_cut s = observed_product_cut (read_authority (legal_reads s))"

definition legal_current_state where
  "legal_current_state s domain asset = get_reg_state (receiver_snapshot (core_regulatory (legal_current_core s))) domain asset"

definition legal_clock where
  "legal_clock s = reservation_clock (machine_state (core_parent (legal_current_core s)))"

definition exact_legal_predecessor where
  "exact_legal_predecessor s order expected action \<longleftrightarrow>
    (\<exists>key event. expected = Some key \<and> legal_predecessor order = Some key \<and>
      committed_legal_events s key = Some event \<and> legal_origin (applied_order event) = key \<and>
      legal_asset (applied_order event) = legal_asset order \<and> legal_action (applied_order event) = action)"

definition recorded_appeal_deadline where
  "recorded_appeal_deadline s asset =
    Option.bind (active_seizure_event s asset)
      (\<lambda>key. Option.bind (committed_legal_events s key) (legal_appeal_deadline \<circ> applied_order))"

definition matching_appeal_deadline where
  "matching_appeal_deadline s order \<longleftrightarrow> legal_appeal_deadline order \<noteq> None \<and>
    legal_appeal_deadline order = recorded_appeal_deadline s (legal_asset order)"

definition appeal_has_elapsed where
  "appeal_has_elapsed s order \<longleftrightarrow> matching_appeal_deadline s order \<and>
    (\<exists>deadline. legal_appeal_deadline order = Some deadline \<and> deadline \<le> legal_clock s)"

definition legal_state_gate where
  "legal_state_gate s order =
    (let mode = legal_current_state s (fst (legal_origin order)) (legal_asset order);
         froze = exact_legal_predecessor s order (active_freeze_event s (legal_asset order)) FREEZE;
         seized = exact_legal_predecessor s order (active_seizure_event s (legal_asset order)) SEIZE
     in case legal_action order of
       FREEZE \<Rightarrow> if mode = Some ACTIVE then Legal_Admit else Legal_Refuse Invalid_Legal_State
     | RESTRICT \<Rightarrow> if mode = Some ACTIVE then Legal_Admit else Legal_Refuse Invalid_Legal_State
     | SEIZE \<Rightarrow> if mode = Some FROZEN \<and> froze then Legal_Admit else Legal_Refuse Missing_Prior_Freeze
     | CONFISCATE \<Rightarrow> if mode \<noteq> Some SEIZED \<or> \<not> seized then Legal_Refuse Missing_Prior_Seizure
       else if \<not> matching_appeal_deadline s order then Legal_Refuse Appeal_Deadline_Mismatch
       else if \<not> appeal_has_elapsed s order then Legal_Refuse Appeal_Still_Open
       else if legal_destination order = None then Legal_Refuse Missing_Confiscation_Destination else Legal_Admit
     | UNFREEZE \<Rightarrow> if mode = Some FROZEN \<and> froze then Legal_Admit else Legal_Refuse Invalid_Legal_State
     | UNRESTRICT \<Rightarrow> if mode = Some RESTRICTED then Legal_Admit else Legal_Refuse Invalid_Legal_State
     | RELEASE \<Rightarrow> if mode = Some SEIZED \<and> seized then Legal_Admit else Legal_Refuse Invalid_Legal_State)"

definition legal_admission_at_cut where
  "legal_admission_at_cut legal_grant order_verified stage entry who order s =
    (if \<not> order_verified stage entry who order \<or> legal_officer order \<noteq> who \<or> legal_basis order = 0 \<or>
       legal_asset order \<notin> legal_scope order \<or>
       \<not> legal_grant stage entry who (legal_jurisdiction order) (legal_asset order) (legal_action order)
           (cut_authority_epoch (legal_current_cut s))
     then Legal_Refuse Invalid_Legal_Authority
     else if (case stage of Legal_Source_Emission \<Rightarrow>
         legal_issuance_epoch order \<noteq> cut_authority_epoch (legal_current_cut s) \<or>
         (issued_legal_orders s (legal_origin order) \<noteq> None \<and> issued_legal_orders s (legal_origin order) \<noteq> Some order)
       | Legal_Receiving_Commit \<Rightarrow> issued_legal_orders s (legal_origin order) \<noteq> Some order)
     then Legal_Refuse Conflicting_Legal_Order else legal_state_gate s order)"

lemma confiscation_requires_current_seizure_and_elapsed_appeal:
  assumes "legal_action order = CONFISCATE" "legal_state_gate s order = Legal_Admit"
  shows "legal_current_state s (fst (legal_origin order)) (legal_asset order) = Some SEIZED \<and>
    exact_legal_predecessor s order (active_seizure_event s (legal_asset order)) SEIZE \<and>
    appeal_has_elapsed s order \<and> legal_destination order \<noteq> None"
  using assms by (auto simp: legal_state_gate_def Let_def split: if_splits)

lemma current_state_without_seizure_gets_its_own_refusal:
  assumes "legal_action order = CONFISCATE"
    "legal_current_state s (fst (legal_origin order)) (legal_asset order) \<noteq> Some SEIZED"
  shows "legal_state_gate s order = Legal_Refuse Missing_Prior_Seizure"
  using assms by (simp add: legal_state_gate_def Let_def)

lemma premature_confiscation_gets_appeal_refusal:
  assumes "legal_action order = CONFISCATE"
    "legal_current_state s (fst (legal_origin order)) (legal_asset order) = Some SEIZED"
    "exact_legal_predecessor s order (active_seizure_event s (legal_asset order)) SEIZE"
    "matching_appeal_deadline s order"
    "legal_appeal_deadline order = Some deadline" "legal_clock s < deadline"
  shows "legal_state_gate s order = Legal_Refuse Appeal_Still_Open"
  using assms by (simp add: legal_state_gate_def appeal_has_elapsed_def Let_def)

lemma shortened_appeal_deadline_cannot_authorize_confiscation:
  assumes "legal_action order = CONFISCATE"
    "legal_current_state s (fst (legal_origin order)) (legal_asset order) = Some SEIZED"
    "exact_legal_predecessor s order (active_seizure_event s (legal_asset order)) SEIZE"
    "legal_appeal_deadline order \<noteq> recorded_appeal_deadline s (legal_asset order)"
  shows "legal_state_gate s order = Legal_Refuse Appeal_Deadline_Mismatch"
  using assms by (simp add: legal_state_gate_def matching_appeal_deadline_def Let_def)

lemma restriction_provenance_cannot_authorize_seizure:
  assumes "legal_action order = SEIZE" "legal_state_gate s order = Legal_Admit"
  shows "\<exists>key event. legal_predecessor order = Some key \<and> committed_legal_events s key = Some event \<and>
    legal_action (applied_order event) = FREEZE"
  using assms by (auto simp: legal_state_gate_def exact_legal_predecessor_def Let_def split: if_splits)

lemma reserved_asset_restriction_uses_the_active_regulatory_state:
  assumes "legal_action order = RESTRICT" "legal_current_state s (fst (legal_origin order)) (legal_asset order) = Some ACTIVE"
  shows "legal_state_gate s order = Legal_Admit"
  using assms by (simp add: legal_state_gate_def Let_def)

end
