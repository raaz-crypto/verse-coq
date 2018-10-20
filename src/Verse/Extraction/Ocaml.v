(* begin hide *)
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


Axiom printstring  : string -> unit.
Axiom writefile    : string -> string -> unit.


Definition print_doc (d:Doc) : unit := printstring (layout d).



Extract Constant writefile   => "fun f s ->
        let listToString cl = String.concat """" (List.map (String.make 1) cl) in
        let out_f = open_out (listToString f) in
            (output_string out_f (listToString s); close_out out_f)".

Extract Constant printstring => "fun x ->
  let listToString cl = String.concat """" (List.map (String.make 1) cl)
  in print_string (listToString x)".

(* end hide *)

(** * Generating the source file.

After the verse program is written and compiled using the appropriate
architecture compiler, we get an object of [prog] of type [Doc +
{CompileError}]. We need to get the actual source (C or assembly) out
of this. The recommended way is to extract an ocaml program for
generating the code. We can either extract a ocaml program that prints
the code to its standard output or a program that writes the code into
a given program file.

 *)

(** ** Printing to standard output

The Coq function given below when extracted will give an ml function that
prints the code to standard output.


*)

Definition print_code {E : Prop} (x: Doc + {E})
  := recover (ap (print_doc) x).

(**

The following code snippet allows extracting an ml program that prints
the source to the standard output.

 *)

(**
<<
Require Import Verse.Extraction.Ocaml.
Definition main : unit := print_code prog.
Extraction "foo.ml" main.
>>
 *)

(**

Running the program foo.ml will print the program on the standard
output.

*)

(** ** Generating program in a file.


The coq function [writeProgram] when extracted gives a ml function
that generates the program in the given file. P The program file
themselves are captured by the inductive type [ProgFile].

*)

Inductive ProgFile :=
| C : string -> ProgFile     (* C "foo" denote the file foo.c *)
| ASM : string -> ProgFile.  (* ASM "foo" denotes the file foo.s *)


Definition writeProgram {E : Prop}(pf : ProgFile) (prog : Doc + {E})
  := let filename := match pf with
                     | C s   => s ++ ".c"
                     | ASM s => s ++ ".s"
                     end%string in
     let prog_str := layout <$> prog in
     let write_it := writefile filename <$> prog_str
     in recover write_it.

(**

The following code snippet allows extracting an ml program that saves
the program in the file "foo.c".

 *)


(**

<<
Require Import Verse.Extraction.Ocaml.
Definition main : unit := writeProgram (C "foo") code.
Extraction "foo.ml" main.
>>

 *)

(**

The execution of "foo.ml" will result in generating the "foo.c" file.

*)
