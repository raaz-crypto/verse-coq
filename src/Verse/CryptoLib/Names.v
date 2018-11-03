Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.

Record Name := { primitive : string;
                 arch : string;
                 features : list string
              }.

Fixpoint concatSep (sep : string)(l : list string) : string :=
  match l with
  | [ ]       => ""
  | [x]       => x
  | (x :: xs) => x ++ sep ++ concatSep sep xs
  end.

Definition details (n : Name) := concatSep "_" (features n).

Definition cFunName (n : Name) : string :=
  concatSep "_" (["verse"%string ; primitive n; arch n] ++ features n)%list.

Definition libVerseFilePath (n : Name) : string :=
  concatSep "/" ["libverse"%string; primitive n; arch n; details n].

Require Import Ascii.
Definition toUpper (c : ascii) : ascii :=
  let Acode := nat_of_ascii "A" in
  let offset := nat_of_ascii c - nat_of_ascii "a" in
  ascii_of_nat (Acode + offset).

Definition capitalize (s : string) :=
  match s with
  | String c xs => String (toUpper c) xs
  | xs          => xs
  end.


Definition raazModule (n : Name) : list string :=
  ["Raaz"; "Verse"]%string ++ List.map capitalize [primitive n; arch n; details n].

Require Import Verse.PrettyPrint.
Require Import Verse.Extraction.Ocaml.


Definition write_module (module : list string)(cont : list Doc) :=
  let mfile := (concatSep "/" ("libverse" :: module) ++ ".hs")%string in
  let mname := concatSep "." module in
  let exts   := [ "DataKinds";
                  "KindSignatures";
                  "ForeignFunctionInterface"
                ]%string in
  let langLine := line <> sepBy (text "," <> line) (List.map text exts) in
  let pragma := vcat [ text "{-# LANGUAGE" <> nest 16 langLine;
                         text "#-}"
                     ] in
  let imports  :=  List.map text [ "import Raaz.Core";
                                     "import Foreign.Ptr";
                                     "import Data.Word"
                                 ]%string in
  let fcontent := text "module" <_> text mname <_> text "where" <> line
                  <> vcat (imports ++ cont)%list in
  let fullcontent := vcat [ pragma; fcontent] in
  writefile mfile (layout fullcontent).
