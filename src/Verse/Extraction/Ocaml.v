Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlZInt.

Require Import Verse.PrettyPrint.
Require Import Verse.Error.

Require Import String.
Extraction Language Ocaml.

Axiom printstring : string -> unit.
Definition print_doc (d:Doc) : unit := printstring (layout d).

Definition print_code {E : Prop} (x: Doc + {E}) := recover (ap (print_doc) x).

Extract Constant printstring => "fun x ->
  let listToString cl = String.concat """" (List.map (String.make 1) cl)
  in print_string (listToString x)".
