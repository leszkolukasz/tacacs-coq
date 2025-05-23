Require Extraction.

Require Export Extracted.Definitions.
Require Export Extracted.CoqPacket.
Require Export Extracted.CoqServer.
Require Export Extracted.CoqDatabase.
Require Export Extracted.CoqUtils.

Require ExtrOcamlBasic.
Require ExtrOCamlInt63.
Require ExtrOcamlZInt.
Require ExtrOcamlIntConv.
Require ExtrOcamlChar.
Require ExtrOcamlString.
Require ExtrOcamlNativeString.

Extraction Blacklist List String Uint63.

(* Unset Extraction Optimize. *)
Set Extraction Output Directory ".".

Extract Inductive Definitions.Result => "Result.t" [ "Result.Ok" "Result.Error" ].
Extract Constant Definitions.file_descr => "Unix.file_descr".
Extract Constant Definitions.sockaddr => "Unix.sockaddr".

Extract Constant Definitions.println => "fun s -> print_string s; print_newline (); flush stdout; true".
(* Extraction Inline Definitions.println. *)
Extract Constant Definitions.int_to_string => "fun i -> string_of_int (Uint63.hash i)".
(* Extraction Inline Definitions.int_to_string. *)
Extract Constant Definitions.eq_sockaddr => "(fun x y -> x = y)".
(* Extraction Inline Definitions.eq_sockaddr. *)

Recursive Extraction Library CoqUtils.
Recursive Extraction Library CoqPacket.
Recursive Extraction Library CoqServer.
Recursive Extraction Library CoqDatabase.
Recursive Extraction Library Definitions.
