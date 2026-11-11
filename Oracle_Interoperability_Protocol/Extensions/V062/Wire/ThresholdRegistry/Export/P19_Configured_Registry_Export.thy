theory P19_Configured_Registry_Export
  imports "OIP_P19_Configured_Registry_G0.P19_Configured_Registry_G0"
    "OIP_P19_Threshold_Export.P19_Threshold_Export"
begin

text \<open>
  The current host selector and configured roster list are independent inputs.
  The existing raw signature step consumes the resulting registry. The alternate
  selector is available for the ambiguity-guard test.
\<close>

type_synonym p19_integer_roster_row = "integer list \<times> (integer \<times> integer list) list"

fun p19_parse_integer_roster_rows :: "p19_integer_roster_row list \<Rightarrow> p19_roster list option" where
  "p19_parse_integer_roster_rows [] = Some []"
| "p19_parse_integer_roster_rows ((row_header,row_members) # remaining) =
    (if length row_header \<noteq> 6 \<or> \<not> p19_integer_nonnegative row_header \<or>
        (\<exists>(i,k) \<in> set row_members. i < 0 \<or> \<not> p19_integer_octets k)
     then None
     else case (p19_export_roster (map nat_of_integer row_header)
                 (map (\<lambda>(i,k). (nat_of_integer i,map nat_of_integer k)) row_members),
                 p19_parse_integer_roster_rows remaining) of
       (Some roster_row, Some parsed_rows) \<Rightarrow> Some (roster_row # parsed_rows)
     | _ \<Rightarrow> None)"

definition p19_registry_integer_identity :: "unit \<Rightarrow> integer list" where
  "p19_registry_integer_identity _ = [1,19,2]"

definition p19_registry_integer_packet ::
  "bool \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> p19_integer_roster_row list \<Rightarrow>
    (integer list \<times> bool) list \<Rightarrow> (integer list \<times> integer list \<times> integer list \<times> bool) list \<Rightarrow>
    integer list \<Rightarrow> (integer list \<times> integer list list) option" where
  "p19_registry_integer_packet remove_ambiguity frame schemes current roster_rows key_checks strict_checks raw =
    (if \<not> p19_export_integer_metadata_ok frame schemes current []
        ([] :: (integer \<times> integer list) list) key_checks strict_checks \<or>
        \<not> p19_integer_octets raw then None else
     case p19_parse_integer_roster_rows roster_rows of None \<Rightarrow> None
       | Some parsed_rows \<Rightarrow>
         let ns = map nat_of_integer;
             current_epoch = p19_current_epoch (p19_export_registry (ns current) [] []);
             registry = (if remove_ambiguity then p19_registry_without_ambiguity_guard current_epoch parsed_rows
                         else p19_registry_from_rows current_epoch parsed_rows);
             keys = map (\<lambda>(k,b). (ns k,b)) key_checks;
             facts = map (\<lambda>(k,m,s,b). (ns k,ns m,ns s,b)) strict_checks;
             (words,blobs) = p19_export_packet (nat_of_integer frame) (ns schemes) registry keys facts (ns raw)
         in Some (map integer_of_nat words,map (map integer_of_nat) blobs))"

lemma p19_exported_step_cannot_accept_ambiguous_current_rows:
  assumes many: "length (p19_rows_at roster_rows
              (p19_core_slot (packet_core packet), wire_authority_epoch (packet_core packet))) > 1"
  shows "\<not> p19_export_is_accept (p19_export_step frame schemes
    (p19_registry_from_rows current_epoch roster_rows) key_checks strict_checks packet)"
proof
  assume accept: "p19_export_is_accept (p19_export_step frame schemes
    (p19_registry_from_rows current_epoch roster_rows) key_checks strict_checks packet)"
  have valid: "p19_threshold_ok (p19_observed_key key_checks) (p19_observed_strict strict_checks)
    (p19_registry_from_rows current_epoch roster_rows) frame (packet_core packet) (packet_signature packet)"
    by (rule p19_export_success_reuses_the_verified_threshold_contract(4)[OF accept])
  from threshold_acceptance_exposes_exact_current_roster_and_signatures[OF valid]
  obtain roster_row where selected: "p19_select (p19_registry_from_rows current_epoch roster_rows)
    (packet_core packet) = Some roster_row" by blast
  from selected many show False
    by (simp add: p19_selecting_configured_roster_consumes_the_unique_exact_row)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms p19_exported_step_cannot_accept_ambiguous_current_rows
      p19_selecting_configured_roster_consumes_the_unique_exact_row
      p19_removing_only_ambiguity_refusal_changes_threshold_acceptance})
  then () else error "Unexpected oracle in configured roster export"
\<close>

export_code p19_registry_integer_identity p19_registry_integer_packet
  in SML module_name OIP_P19_Configured_Registry file_prefix "oip_p19_configured_registry"

end
