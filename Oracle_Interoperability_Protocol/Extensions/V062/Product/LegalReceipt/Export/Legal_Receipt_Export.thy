theory Legal_Receipt_Export
  imports "OIP_Legal_Receipt_Check.Legal_Receipt_Check"
begin

fun lr_reply_words where
  "lr_reply_words LR_Invalid_Authority = [(0::nat),0,0]"
| "lr_reply_words LR_Unavailable = [1,0,0]"
| "lr_reply_words LR_Conflicting_Order = [2,0,0]"
| "lr_reply_words (LR_Retained (lr_tag,lr_value)) = [3,lr_tag,lr_value]"
| "lr_reply_words LR_Fresh = [4,0,0]"

definition lr_observe_words where
  "lr_observe_words lr_header lr_order lr_payload lr_old_order lr_old_payload =
    (case lr_header of [lr_admitted,lr_up,lr_other_claim,lr_stage,lr_present,lr_old_stage,lr_tag,lr_value] \<Rightarrow>
      (if \<not> list_all (\<lambda>lr_flag. lr_flag \<le> 1) [lr_admitted,lr_up,lr_other_claim,lr_present]
       then None else
         let lr_stored = (if lr_present = 1 then Some (lr_old_stage,lr_old_order,lr_old_payload,(lr_tag,lr_value)) else None)
         in Some (concat (map (\<lambda>lr_check.
           lr_reply_words (lr_selection lr_check (lr_admitted = 1) (lr_up = 1) (lr_other_claim = 1)
             lr_stage lr_order lr_payload lr_stored)) [True, False])))
     | _ \<Rightarrow> None)"

definition lr_observe_integer :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "lr_observe_integer lr_header lr_order lr_payload lr_old_order lr_old_payload =
    (if list_all (\<lambda>lr_word. 0 \<le> lr_word) (lr_header @ lr_order @ lr_payload @ lr_old_order @ lr_old_payload)
     then map_option (map integer_of_nat) (lr_observe_words (map nat_of_integer lr_header) (map nat_of_integer lr_order)
        (map nat_of_integer lr_payload) (map nat_of_integer lr_old_order) (map nat_of_integer lr_old_payload))
     else None)"

export_code lr_observe_integer in SML module_name OIP_Legal_Receipt file_prefix "oip_legal_receipt"

end
