Require Import String.
Require Import Ascii.
Require Import NPeano.
Require Import Peano_dec.
Import  List.ListNotations.
Require Import Verse.Types.

(* A nibble, i.e. 4 bytes. *)
Inductive Nibble :=
| x0
| x1
| x2
| x3
| x4
| x5
| x6
| x7
| x8
| x9
| xA
| xB
| xC
| xD
| xE
| xF
.

Definition Nibbles := list Nibble.
(** A constant is either a word or a vector of appropriate type *)
Inductive constant  : type value -> Type :=
| w (n : nat)   : forall l : Nibbles, List.length l = 2^(S n)
                -> constant (Word n)
| v {m n : nat} : Vector.t (constant (Word n)) (2 ^ m)
                  -> constant (vector m n).

(** * Internal module.

 Lots of helper types and functions. Otherwise un-interesting

*)

Module Internal.

  Open Scope char_scope.

  (** Convert digit to Nibble *)
  Definition hexDigit (c : ascii) : option Nibble :=
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

  (* Convert Nibble back to ascii *)
  Definition NibbletoAscii (x : Nibble) : ascii :=
    match x with
      | x0 => "0"
      | x1 => "1"
      | x2 => "2"
      | x3 => "3"
      | x4 => "4"
      | x5 => "5"
      | x6 => "6"
      | x7 => "7"
      | x8 => "8"
      | x9 => "9"
      | xA => "a"
      | xB => "b"
      | xC => "c"
      | xD => "d"
      | xE => "e"
      | xF => "f"
    end.

  (** Convert a vector of Nibbles to the corresponding string *)
  Fixpoint NibblestoString (l : Nibbles) : string :=
    match l with
      | nil         => EmptyString
      | cons x xs => String (NibbletoAscii x) (NibblestoString xs)
    end.

  Definition comb (ox : option Nibble)(oxs : option Nibbles)
  : option (Nibbles) :=
    match ox, oxs with
      | Some x, Some xs => Some (cons x xs)
      | _, _ => None
    end.

  Fixpoint parse (s : string) : option Nibbles :=
    match s with
      | EmptyString => Some nil
      | String x xs => comb (hexDigit x) (parse xs)
    end.

  Definition fromOption {A : Type}(op : option A)
  : match op with
      | None   => option A
      | Some _ => A
    end :=
    match op with
      | None   => None
      | Some x => x
    end.

  Ltac crush_hex_proofs :=
    repeat simpl;trivial;
    repeat match goal with
             | [ H  : _      |-  _ ] => rewrite H
             | _
               => simpl; autorewrite with hexhints; auto
           end.

  Lemma hexDigit_o_toAscii_isId:
    forall x : Nibble, hexDigit (NibbletoAscii x) = Some x.
  Proof.
    intros. induction x; crush_hex_proofs.
  Qed.
  Hint Rewrite hexDigit_o_toAscii_isId : hexhints.
  Theorem correct_parse :
    forall (v : Nibbles), parse (NibblestoString v) = Some v.
  Proof.
    intro v.
    induction v; crush_hex_proofs.
  Qed.

  Definition parseC (n : nat)(s : string) : option (constant (Word n)) :=
  match parse s with
      | None     => None
      | Some res
        => match eq_nat_dec (List.length res)(2^S n) with
             | left pf => Some (w n res pf)
             | _       => None
           end
  end.


  Definition hex (s : string) := fromOption  (parse s).

End Internal.
Import Internal.

(* Constructs a word constant *)
Definition wc (n : nat)(s : string) := fromOption (parseC n s).
