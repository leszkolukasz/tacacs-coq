Require Extraction.

Require Export Extracted.CoqServer.
Require Export Extracted.Protocol.

Require ExtrOcamlBasic.
Require ExtrOCamlInt63.
Require ExtrOcamlZInt.
Require ExtrOcamlIntConv.
Require ExtrOcamlChar.
Require ExtrOcamlString.
Require ExtrOcamlNativeString.

Extraction Blacklist List String Uint63.

Set Extraction Output Directory ".".

(* Extract Constant Uint63.int => "Override.i". *)
(* Extract Constant oint => "int". *)

(* Extraction Inline Uint63.int. *)

Recursive Extraction Library CoqServer.
Recursive Extraction Library Protocol.
