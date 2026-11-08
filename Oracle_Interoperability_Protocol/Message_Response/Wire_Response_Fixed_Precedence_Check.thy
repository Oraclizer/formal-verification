theory Wire_Response_Fixed_Precedence_Check
  imports Wire_Response_Fixed_Check
begin

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
    response_fixed_expected_then_caller_is_the_existing_source_projection
    response_fixed_actual_expected_and_caller_keep_the_original_call_id
    response_fixed_existing_caller_success_has_an_actual_expected_decoding
    response_fixed_expected_query_decode_is_read_or_format_error
    response_fixed_expected_query_eight_fails_before_byte_comparison
    response_fixed_expected_decode_error_precedes_original_byte_comparison
    response_fixed_original_mismatch_precedes_caller_projection
    response_fixed_matching_original_reaches_the_actual_caller_projection})
  then () else error "Unexpected oracle in expected decode and original/caller short-circuit ordering"
\<close>

text \<open>
  The Rust sequence is response operand decode, expected depth1 decode,
  raw original mismatch, caller projection, id mismatch, status/compatibility.
  A successful Query read with another embedded original reaches replay76
  before its missing caller; Query8 fails expected depth1 decode70 first.
  These statements describe model-level validation order; they do not
  establish signature correctness or implementation conformance.
\<close>

end
