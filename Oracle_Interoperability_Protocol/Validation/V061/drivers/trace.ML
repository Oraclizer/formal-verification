val _ = use (valOf (OS.Process.getEnv "OIP_SYNC_PRODUCT_MODEL"));
val _ = use (valOf (OS.Process.getEnv "OIP_SYNC_PRODUCT_INPUT"));

fun hexByte byte =
  let
    val n = IntInf.toInt byte;
    val alphabet = "0123456789abcdef";
  in
    if 0 <= n andalso n < 256 then
      String.implode [String.sub (alphabet, n div 16), String.sub (alphabet, n mod 16)]
    else raise Fail "Non-octet in model output"
  end;

fun hex bytes = String.concat (map hexByte bytes);
fun words values = String.concatWith "," (map IntInf.toString values);
fun blobs values = String.concatWith "," (map hex values);
fun printRow (id, ((resultWords, resultBlobs), (stateWords, stateBlobs))) =
  print (String.concatWith "\t" ["O",id,words resultWords,blobs resultBlobs,words stateWords,blobs stateBlobs] ^ "\n");

val _ =
  case productModelRows of
    NONE => raise Fail "Product model did not decode the context"
  | SOME rows => ListPair.appEq printRow (productCaseIds, rows);
