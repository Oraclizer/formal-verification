fun threshold_env name =
  case OS.Process.getEnv name of SOME path => path | NONE => raise Fail ("Missing " ^ name);
val _ = use (threshold_env "OIP_THRESHOLD_RAW_MODEL");

fun threshold_identity_text bytes = String.implode (map (fn byte =>
  if byte < 32 orelse byte > 126 then raise Fail "Invalid threshold model identity text"
  else Char.chr (IntInf.toInt byte)) bytes);
val _ = let
  val fields = map threshold_identity_text (OIP_Threshold_Raw_ABI.threshold_raw_model_identity ());
  val _ = if List.length fields = 6 then () else raise Fail "Wrong threshold model identity shape";
in
  print (String.concatWith "\t" ("OIP-MODEL" :: fields) ^ "\n")
end;

fun threshold_words values = "[" ^ String.concatWith ","
  (map (fn value => "\"" ^ IntInf.toString value ^ "\"") values) ^ "]";
fun threshold_hex bytes = String.concat (map (fn value =>
  if value < 0 orelse value > 255 then raise Fail "Non-octet threshold output"
  else String.map Char.toLower (StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (IntInf.toInt value)))) bytes);
fun threshold_emit identifier result =
  let val prefix = "OIP-THRESHOLD\t{\"id\":\"" ^ identifier ^ "\""
  in case result of NONE => print (prefix ^ ",\"abi_invalid\":true}\n")
   | SOME (words, blobs) => print (prefix ^ ",\"words\":" ^ threshold_words words ^
       ",\"blobs_hex\":[" ^ String.concatWith "," (map (fn bytes => "\"" ^ threshold_hex bytes ^ "\"") blobs) ^ "]}\n")
  end;
val _ = use (threshold_env "OIP_THRESHOLD_RAW_INPUTS");
