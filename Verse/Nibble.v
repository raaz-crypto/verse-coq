Require Import String.
Require Import Ascii.
Require Import NPeano.
Require Import Verse.Tactics.
Require Import Verse.BinTree.
Require Import Verse.Error.
Import List.ListNotations.


(** A nibble, i.e. 4 bytes. *)
Inductive nibble := x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9
| xA | xB | xC | xD | xE | xF.

(** A list of nibbles *)
Definition nibbles := list nibble.

(** * Internal module.

 Lots of helper types and functions. Otherwise un-interesting

*)

Module Internal.

  Open Scope char_scope.
  Definition nibbleToAscii (nib : nibble) : ascii :=
    match nib with
      | x0  => "0"
      | x1  => "1"
      | x2  => "2"
      | x3  => "3"
      | x4  => "4"
      | x5  => "5"
      | x6  => "6"
      | x7  => "7"
      | x8  => "8"
      | x9  => "9"
      | xA => "a"
      | xB => "b"
      | xC => "c"
      | xD => "d"
      | xE => "e"
      | xF => "f"
    end.

  (** Convert digit to Nibble *)
  Definition hexDigit (c : ascii) : option nibble :=
    match c with
    | "0" => Some x0
    | "1" => Some x1
    | "2" => Some x2
    | "3" => Some x3
    | "4" => Some x4
    | "5" => Some x5
    | "6" => Some x6
    | "7" => Some x7
    | "8" => Some x8
    | "9" => Some x9
    | "a" | "A" => Some xA
    | "b" | "B" => Some xB
    | "c" | "C" => Some xC
    | "d" | "D" => Some xD
    | "e" | "E" => Some xE
    | "f" | "F" => Some xF
    | _ => None
  end.

  (** Convert a vector of Nibbles to the corresponding string *)
  Fixpoint nibblesToString (l : nibbles) : string :=
    match l with
      | nil       => EmptyString
      | cons x xs => String (nibbleToAscii x) (nibblesToString xs)
    end.


  Definition comb (ox : option nibble)(oxs : option nibbles)
  : option (nibbles) :=
    match ox, oxs with
      | Some x, Some xs => Some (cons x xs)
      | _, _ => None
    end.


End Internal.

Import Internal.

Fixpoint parse (s : string) : option nibbles :=
  match s with
    | EmptyString => Some nil
    | String x xs => comb (hexDigit x) (parse xs)
  end.

Module Correctness.
  (** Correctness proofs for functions here. Not very useful *)
  Lemma hexDigit_o_toAscii_isId:
    forall x : nibble, hexDigit (nibbleToAscii x) = Some x.
  Proof.
    intro x. induction x; compute; trivial.
  Qed.

  Hint Rewrite hexDigit_o_toAscii_isId.
  Theorem correct_parse :
    forall (v : nibbles), parse (nibblesToString v) = Some v.
  Proof.
    intro v.
    induction v; rewrite_equalities.
  Qed.

End Correctness.