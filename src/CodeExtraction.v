Require Extraction.

Require Export Extracted.Definitions.
Require Export Extracted.CoqPacket.
Require Export Extracted.CoqServer.

Require ExtrOcamlBasic.
Require ExtrOCamlInt63.
Require ExtrOcamlZInt.
Require ExtrOcamlIntConv.
Require ExtrOcamlChar.
Require ExtrOcamlString.
Require ExtrOcamlNativeString.

Extraction Blacklist List String.

Set Extraction Output Directory ".".

Extract Inductive Definitions.Result => "Result.t" [ "Result.Ok" "Result.Error" ].
Extract Constant Definitions.file_descr => "Unix.file_descr".
Extract Constant Definitions.sockaddr => "Unix.sockaddr".

Recursive Extraction Library CoqPacket.
Recursive Extraction Library CoqServer.
Recursive Extraction Library Definitions.
