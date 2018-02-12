(* begin hide *)
Require Import Bvector.
Require Import Verse.Error.
Require Import Vector.
Require Import Coq.NArith.Ndigits.
Require Import BinNums.
Require Import BigNumPrelude.
Require Import String.
Require Import Ascii.
Require Import Verse.PrettyPrint.
Local Open Scope N_scope.
(* end hide *)

(** * Words.

We give an implementation of n-bit words that is useful in to capture
the meanings of

*)



Inductive t (n : nat) : Type :=
| bits : Bvector n -> t n.

Arguments bits [n] _.

(** Words measured in units of bytes *)
Definition bytes n := t (8 * n).


(* Errors while encoding *)
Inductive EncodeError : Prop := BadBase16 | BadBinary | TooFewDigits | TooManyDigits.

(* begin hide *)
Definition toN {n}(x : t n) :=
  match x with
  | bits bv => Bv2N n bv
  end.

Open Scope string_scope.

Module Base16.


  Open Scope string_scope.
  Open Scope char_scope.


    Definition hexDigit (c : ascii) : N + {EncodeError}:=
    (match c with
     | "0" => inleft 0
     | "1" => inleft 1
     | "2" => inleft 2
     | "3" => inleft 3
     | "4" => inleft 4
     | "5" => inleft 5
     | "6" => inleft 6
     | "7" => inleft 7
     | "8" => inleft 8
     | "9" => inleft 9
     | "a" | "A" => inleft 10
     | "b" | "B" => inleft 11
     | "c" | "C" => inleft 12
     | "d" | "D" => inleft 13
     | "e" | "E" => inleft 14
     | "f" | "F" => inleft 15
     | _ => inright BadBase16
     end)%N.

    Fixpoint hexToNP (sofar : N) (s : string) :=
      let update := (fun x => sofar * 16 + x)%N in
      match s with
      | String c sp => x <- update <$> hexDigit c ;  hexToNP x sp
      | EmptyString => inleft sofar
      end.

    Fixpoint trim_separators (s : string) : string:=
      match s with
      | EmptyString => EmptyString
      | String c sp => match c with
                       | " " | "_" | ":" | "-" => trim_separators sp
                       | _                     => String c (trim_separators sp)
                       end
      end.

    Definition hexToN (n : nat)(s : string) : t n + {EncodeError}
      := match Nat.compare n (4 * String.length s) with
         | Eq => @bits n <$> (N2Bv_gen n <$> hexToNP (0%N) s)
         | Lt => inright TooManyDigits
         | Gt => inright TooFewDigits
         end.

    Definition lastHexDigit a :=
      match Bv2N 4 (N2Bv_gen 4 a) with
       | 0 => "0"
       | 1 => "1"
       | 2 => "2"
       | 3 => "3"
       | 4 => "4"
       | 5 => "5"
       | 6 => "6"
       | 7 => "7"
       | 8 => "8"
       | 9 => "9"
       | 10 => "a"
       | 11 => "b"
       | 12 => "c"
       | 13 => "d"
       | 14 => "e"
       | 15 => "f"
       | _  => "-"
      end.
    Fixpoint NToHex (n : nat)(a : N) : string :=
      match n with
      | 0%nat             => EmptyString
      | (S (S (S (S m)))) => NToHex m (a / 16) ++ String (lastHexDigit a) EmptyString
      | _                 => String (lastHexDigit a) EmptyString
      end.

End Base16.

(* end hide *)

(** ** Base16 representation.

We define a convenient function to represent word constants in hex
notation. A 16-bit word of value AABB (in hex notation) can be
represented as [Ox "aabb"].

*)

Definition Ox s := let t := Base16.trim_separators s
                   in recover (Base16.hexToN (4 * String.length t) t).

(**

Conversely we can convert a word constant to its hexadecimal string as
follows:

*)
Definition hex {n} (u : t n) : string:=
  match u with
  | bits bv => Base16.NToHex n (Bv2N n bv)
  end.


(** This function lifts a numeric binary function to the word type *)
Definition numBinOp {n} f  (x y : t n) : t n :=
  match x, y with
  | bits xv, bits yv => bits (N2Bv_gen n (f (Bv2N n xv)(Bv2N n yv)))
  end.

(** This function lifts a numeric unary function to the word type *)
Definition numUnaryOp {n : nat} f (x : t n) : t n :=
  match x with
  | bits xv => bits (N2Bv_gen n (f (Bv2N n xv)))
  end.


(** We also give a way to define bitwise operations on the t type *)

Definition bitwiseBinOp {n : nat} f (x y : t n) : t n :=
  match x,y with
  | bits xv, bits yv => bits (Vector.map2 f xv yv)
  end.

Definition bitwiseUnaryOp {n : nat} f (x : t n) : t n :=
  match x with
  | bits xv => bits (Vector.map f xv )
  end.

Instance word_pretty (n : nat) : PrettyPrint (t n) := { doc := fun w => doc (@hex n w) }.
