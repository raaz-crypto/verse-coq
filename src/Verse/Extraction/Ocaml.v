Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlZInt.

Require Import Verse.PrettyPrint.

Extraction Language Ocaml.

Axiom print_code : unit.

Extract Constant print_code => "fun code ->
  let listToString cl = String.concat """" (List.map (String.make 1) cl)
  in print_string (listToString (tryLayout code));;".
