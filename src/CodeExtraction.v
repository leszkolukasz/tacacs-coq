Require Extraction.

Require Export Extracted.Definitions.
Require Export Extracted.CoqPacket.
Require Export Extracted.CoqServer.
Require Export Extracted.CoqDatabase.
Require Export Extracted.CoqUtils.
Require Export Extracted.CoqClient.
Require Export Extracted.CoqLemmas.

Require ExtrOcamlBasic.
Require ExtrOCamlInt63.
Require ExtrOcamlZInt.
Require ExtrOcamlIntConv.
Require ExtrOcamlChar.
Require ExtrOcamlString.
Require ExtrOcamlNativeString.

Extraction Blacklist List String Uint63 Sint63.

(* Unset Extraction Optimize. *)
Set Extraction Output Directory ".".

Extract Inductive Definitions.Result => "Result.t" [ "Result.Ok" "Result.Error" ].
Extract Constant Definitions.file_descr => "Unix.file_descr".
Extract Constant Definitions.sockaddr => "Unix.sockaddr".

Extract Constant Definitions.println => "
fun s -> let time = Unix.localtime (Unix.time ()) in
    Printf.printf ""\027[36m[%02d:%02d:%02d]\027[0m %s\n%!"" time.Unix.tm_hour time.Unix.tm_min time.Unix.tm_sec s; true".

Extract Constant sockaddr_to_string => "
fun addr ->
  match addr with
  | Unix.ADDR_INET (inet_addr, port) ->
      Printf.sprintf ""ADDR_INET: %s:%d\n%!"" (Unix.string_of_inet_addr inet_addr) port
  | Unix.ADDR_UNIX path ->
      Printf.sprintf ""ADDR_UNIX: %s\n%!"" path
".

Extract Constant Definitions.int_to_string => "fun i -> string_of_int (Uint63.hash i)".
Extract Constant Definitions.eq_sockaddr => "(fun x y -> x = y)".

Recursive Extraction Library CoqUtils.
Recursive Extraction Library CoqPacket.
Recursive Extraction Library CoqServer.
Recursive Extraction Library CoqClient.
Recursive Extraction Library CoqDatabase.
Recursive Extraction Library CoqLemmas.
Recursive Extraction Library Definitions.
