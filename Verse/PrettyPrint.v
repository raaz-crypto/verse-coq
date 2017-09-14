Require Import String.
Require Import Strings.Ascii.
Require Import List.
Require Import NPeano.
Import ListNotations.

(* Wadler Pretty printer *)

Inductive Doc :=
| NilDoc : Doc
| Text   : string -> Doc -> Doc
| Line   : nat    -> Doc -> Doc
.

Definition empty : Doc := NilDoc.

Definition text (s : string) : Doc := Text s empty.
Definition line : Doc              := Line 0 empty.

Fixpoint nest n (d : Doc) : Doc :=
  match d with
  | Text s dp => Text s (nest n dp)
  | Line i dp => Line (n + i) (nest n dp)
  | NilDoc => NilDoc
  end.


Fixpoint spaces (n : nat) : string :=
  match n with
  | 0    => ""
  | S m  => " " ++ spaces m
  end.

Fixpoint layout (d : Doc) : string :=
  let newline := String (ascii_of_nat 10) EmptyString in
  match d with
  | Text s dp => s ++ layout dp
  | Line i dp => newline ++ spaces i ++ layout dp
  | NilDoc    => ""
  end.

Fixpoint append (a b : Doc) : Doc :=
  match a with
  | Text s dp => Text s (append dp b)
  | Line i dp => Line i (append dp b)
  | _         => b
  end.

Fixpoint appendSpace (a b : Doc) : Doc :=
  match b with
  | NilDoc => a
  | _ => match a with
         | Text s NilDoc  => append (text (s ++ " ")) b
         | Text s dp      => Text s (appendSpace dp b)
         | Line i dp => Line i (appendSpace dp b)
         | _         => b
         end
  end.

Notation  "A <>  B" := (append A B).
Notation  "A <_> B" :=  (appendSpace A B) (at level 70).

Definition combine (docs : list Doc) : Doc := List.fold_left append docs empty.
Definition between (b e : string) (doc : Doc) := text b <> doc <> text e.

Fixpoint sepBy (s : Doc) (docs : list Doc) : Doc :=
  match docs with
  | []        => empty
  | [x]       => x
  | (x :: xs) => (x <> s) <_> sepBy s xs
  end.

Fixpoint sepEndBy (s : Doc) (docs : list Doc) : Doc :=
  List.fold_left appendSpace (List.map (fun x => x <> s) docs) empty.

Definition commaSep   := sepBy    (text ",").
Definition semiSep    := sepBy    (text ";").
Definition semiEndSep := sepEndBy (text ";").
Definition lineSep    := sepBy line.

Definition paren   := between "(" ")".
Definition bracket := between "[" "]".
Definition brace   := between "{" "}".


Module Internal.

  Definition digit (n : nat) : ascii :=
    match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
    end.


  Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
    let acc' := String (digit (n mod 10)) acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
      | 0 => acc'
      | n' => writeNatAux time' n' acc'
      end
    end.

  Definition nat_to_str (n : nat) : string :=
    writeNatAux n n "".

End Internal.

Definition decimal n := text (Internal.nat_to_str n).

Class PrettyPrint a := { doc : a -> Doc}.

Instance string_pretty : PrettyPrint string := { doc := text }.
Instance nat_pretty    : PrettyPrint nat    := { doc := decimal }.
