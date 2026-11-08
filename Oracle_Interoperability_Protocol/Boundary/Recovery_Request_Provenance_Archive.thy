theory Recovery_Request_Provenance_Archive
  imports "Recovery_Request_Provenance_Witness"
begin

definition archive_has_ask_witness where
  "archive_has_ask_witness step R0 requests disk \<longleftrightarrow>
    (\<forall>h record. flushed_records disk h = Some record \<longrightarrow>
      state_has_ask_witness step R0 requests (image_records record))"

definition boundary_has_ask_provenance where
  "boundary_has_ask_provenance step R0 requests s \<longleftrightarrow>
    (\<forall>h R. sys_endpoint s = Some (h, R) \<longrightarrow> state_has_ask_witness step R0 requests R) \<and>
    (\<forall>prepared \<in> set (sys_staged s).
      state_has_ask_witness step R0 requests (image_records (staged_record prepared))) \<and>
    archive_has_ask_witness step R0 requests (sys_disk s) \<and>
    (\<forall>disk \<in> set (ghost_disks s). archive_has_ask_witness step R0 requests disk)"

lemma archive_ask_witness_append_right:
  "archive_has_ask_witness step R0 requests disk \<Longrightarrow>
    archive_has_ask_witness step R0 (requests @ suffix) disk"
proof -
  assume old: "archive_has_ask_witness step R0 requests disk"
  have records: "\<forall>h record. flushed_records disk h = Some record \<longrightarrow>
      state_has_ask_witness step R0 requests (image_records record)"
    using old unfolding archive_has_ask_witness_def .
  show "archive_has_ask_witness step R0 (requests @ suffix) disk"
    unfolding archive_has_ask_witness_def
  proof (intro allI impI)
    fix h entry
    assume lookup: "flushed_records disk h = Some entry"
    have base: "state_has_ask_witness step R0 requests (image_records entry)"
      by (rule records[rule_format, OF lookup])
    show "state_has_ask_witness step R0 (requests @ suffix) (image_records entry)"
      by (rule ask_witness_append_right[OF base])
  qed
qed

lemma boundary_ask_provenance_append_right:
  "boundary_has_ask_provenance step R0 requests s \<Longrightarrow>
    boundary_has_ask_provenance step R0 (requests @ suffix) s"
proof -
  assume old: "boundary_has_ask_provenance step R0 requests s"
  have parts:
    "(\<forall>h R. sys_endpoint s = Some (h, R) \<longrightarrow> state_has_ask_witness step R0 requests R) \<and>
     (\<forall>prepared \<in> set (sys_staged s).
       state_has_ask_witness step R0 requests (image_records (staged_record prepared))) \<and>
     archive_has_ask_witness step R0 requests (sys_disk s) \<and>
     (\<forall>disk \<in> set (ghost_disks s). archive_has_ask_witness step R0 requests disk)"
    using old unfolding boundary_has_ask_provenance_def .
  note endpoint = conjunct1[OF parts]
  note remaining = conjunct2[OF parts]
  note staged = conjunct1[OF remaining]
  note storage = conjunct2[OF remaining]
  note current = conjunct1[OF storage]
  note history = conjunct2[OF storage]
  show "boundary_has_ask_provenance step R0 (requests @ suffix) s"
    unfolding boundary_has_ask_provenance_def
  proof (intro conjI)
    show "\<forall>h R. sys_endpoint s = Some (h, R) \<longrightarrow>
        state_has_ask_witness step R0 (requests @ suffix) R"
    proof (intro allI impI)
      fix h R
      assume present: "sys_endpoint s = Some (h, R)"
      have base: "state_has_ask_witness step R0 requests R"
        by (rule endpoint[rule_format, OF present])
      show "state_has_ask_witness step R0 (requests @ suffix) R"
        by (rule ask_witness_append_right[OF base])
    qed
    show "\<forall>prepared \<in> set (sys_staged s).
        state_has_ask_witness step R0 (requests @ suffix) (image_records (staged_record prepared))"
    proof (intro ballI)
      fix prepared
      assume member: "prepared \<in> set (sys_staged s)"
      have base: "state_has_ask_witness step R0 requests (image_records (staged_record prepared))"
        by (rule staged[rule_format, OF member])
      show "state_has_ask_witness step R0 (requests @ suffix) (image_records (staged_record prepared))"
        by (rule ask_witness_append_right[OF base])
    qed
    show "archive_has_ask_witness step R0 (requests @ suffix) (sys_disk s)"
      by (rule archive_ask_witness_append_right[OF current])
    show "\<forall>disk \<in> set (ghost_disks s). archive_has_ask_witness step R0 (requests @ suffix) disk"
    proof (intro ballI)
      fix disk
      assume member: "disk \<in> set (ghost_disks s)"
      have base: "archive_has_ask_witness step R0 requests disk"
        by (rule history[rule_format, OF member])
      show "archive_has_ask_witness step R0 (requests @ suffix) disk"
        by (rule archive_ask_witness_append_right[OF base])
    qed
  qed
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms archive_ask_witness_append_right boundary_ask_provenance_append_right})
  then () else error "Unexpected oracle in Recovery_Request_Provenance_Archive"
\<close>

end
