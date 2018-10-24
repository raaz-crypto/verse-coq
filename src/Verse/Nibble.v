Require Vector.
Import Vector.VectorNotations.
Require Import Ascii.
Require Import String.
Require Import Verse.Error.
Require Import BinNums.
Require Import BigNumPrelude. (* For versions 8.5 and 8.6 versions *)

Inductive Nibble
  := x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 |
     xA | xB | xC | xD | xE | xF.

Definition bytes n := Vector.t Nibble (2 * n).

(* Errors while encoding *)
Inductive EncodeError : Prop := BadBase16 | TooFewDigits | TooManyDigits.

(* begin hide *)
Module Internal.

  Definition toChar (n : Nibble) : ascii :=
    match n with
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

  Local Open Scope char_scope.
    Definition fromChar (c : ascii) : Nibble + {EncodeError}:=
      match c with
       | "0" => inleft x0
       | "1" => inleft x1
       | "2" => inleft x2
       | "3" => inleft x3
       | "4" => inleft x4
       | "5" => inleft x5
       | "6" => inleft x6
       | "7" => inleft x7
       | "8" => inleft x8
       | "9" => inleft x9
       | "a" | "A" => inleft xA
       | "b" | "B" => inleft xB
       | "c" | "C" => inleft xC
       | "d" | "D" => inleft xD
       | "e" | "E" => inleft xE
       | "f" | "F" => inleft xF
       | _ => inright BadBase16
      end.

    Fixpoint trim_separators (s : string) : string :=
      match s with
      | EmptyString => EmptyString
      | String c sp => match c with
                       | " " | "_" | ":" | "-" => trim_separators sp
                       | _                     => String c (trim_separators sp)
                       end
      end.

    Fixpoint fromString (n : nat)(s : string) : Vector.t Nibble n + {EncodeError} :=
      match s,n with
      | String x xs, (S m) => h <- fromChar x;
                                hs <- fromString m xs;
                                {- h :: hs -}

      | String _ _, 0      => error TooFewDigits
      | EmptyString, (S _) => error TooManyDigits
      | EmptyString, 0     => {- [] -}
      end%nat.

    Fixpoint toString {n} (v : Vector.t Nibble n) :=
      match v with
      | [] => EmptyString
      | (x :: xs) => String (toChar x) (toString xs)
      end.

    Definition nibbleToN (x : Nibble) :=
      match x with
       | x0 => 0
       | x1 => 1
       | x2 => 2
       | x3 => 3
       | x4 => 4
       | x5 => 5
       | x6 => 6
       | x7 => 7
       | x8 => 8
       | x9 => 9
       | xA => 10
       | xB => 11
       | xC => 12
       | xD => 13
       | xE => 14
       | xF => 15
       end%N.

End Internal.

(* end hide *)

(** ** Base16 representation.

We define a convenient function to represent word constants in hex
notation. A 16-bit word of value AABB (in hex notation) can be
represented as [Ox "aabb"].

*)

Definition Ox s := let t := Internal.trim_separators s
                   in recover (Internal.fromString (String.length t) t).

Require Import Verse.PrettyPrint.
Instance pretty_print (n : nat) : PrettyPrint (Vector.t Nibble n) :=
  { doc := fun v => text (Internal.toString v) }.

Definition toN {n} : Vector.t Nibble n -> N :=
  (let fldr := fun m x =>  16 * m + Internal.nibbleToN x in
  Vector.fold_left fldr 0)%N.
