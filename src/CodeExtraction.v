Require Extraction.

Require Export Extracted.Definitions.
Require Export Extracted.CoqPacket.
Require Export Extracted.CoqServer.
Require Export Extracted.CoqUtils.

Require ExtrOcamlBasic.
Require ExtrOCamlInt63.
Require ExtrOcamlZInt.
Require ExtrOcamlIntConv.
Require ExtrOcamlChar.
Require ExtrOcamlString.
Require ExtrOcamlNativeString.

Extraction Blacklist List String Uint63.

Set Extraction Output Directory ".".

Extract Inductive Definitions.Result => "Result.t" [ "Result.Ok" "Result.Error" ].
Extract Constant Definitions.file_descr => "Unix.file_descr".
Extract Constant Definitions.sockaddr => "Unix.sockaddr".

Extract Constant Definitions.println => "fun s -> print_string s; print_newline (); flush stdout".

Recursive Extraction Library CoqUtils.
Recursive Extraction Library CoqPacket.
Recursive Extraction Library CoqServer.
Recursive Extraction Library Definitions.
