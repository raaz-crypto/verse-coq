Require Vector.
Import Vector.VectorNotations.
Require Import Ascii.
Require Import String.
Require Import Verse.Error.
Require Import BinNums.
Require Import NArith.

Inductive Nibble
  := Ox0 | Ox1 | Ox2 | Ox3 | Ox4 | Ox5 | Ox6 | Ox7 | Ox8 | Ox9 |
     OxA | OxB | OxC | OxD | OxE | OxF.

Definition bytes n := Vector.t Nibble (2 * n).

(* Errors while encoding *)
Inductive EncodeError : Prop := BadBase16 | TooFewDigits | TooManyDigits.

(* begin hide *)
Module Internal.

  Definition toChar (n : Nibble) : ascii :=
    match n with
    | Ox0 => "0"
    | Ox1 => "1"
    | Ox2 => "2"
    | Ox3 => "3"
    | Ox4 => "4"
    | Ox5 => "5"
    | Ox6 => "6"
    | Ox7 => "7"
    | Ox8 => "8"
    | Ox9 => "9"
    | OxA => "a"
    | OxB => "b"
    | OxC => "c"
    | OxD => "d"
    | OxE => "e"
    | OxF => "f"
    end.

  Local Open Scope char_scope.
    Definition fromChar (c : ascii) : Nibble + {EncodeError}:=
      match c with
       | "0" => inleft Ox0
       | "1" => inleft Ox1
       | "2" => inleft Ox2
       | "3" => inleft Ox3
       | "4" => inleft Ox4
       | "5" => inleft Ox5
       | "6" => inleft Ox6
       | "7" => inleft Ox7
       | "8" => inleft Ox8
       | "9" => inleft Ox9
       | "a" | "A" => inleft OxA
       | "b" | "B" => inleft OxB
       | "c" | "C" => inleft OxC
       | "d" | "D" => inleft OxD
       | "e" | "E" => inleft OxE
       | "f" | "F" => inleft OxF
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
       | Ox0 => 0
       | Ox1 => 1
       | Ox2 => 2
       | Ox3 => 3
       | Ox4 => 4
       | Ox5 => 5
       | Ox6 => 6
       | Ox7 => 7
       | Ox8 => 8
       | Ox9 => 9
       | OxA => 10
       | OxB => 11
       | OxC => 12
       | OxD => 13
       | OxE => 14
       | OxF => 15
      end%N.

    Definition NToNibble (x : N) :=
      match x with
       | 0  => Ox0
       | 1  => Ox1
       | 2  => Ox2
       | 3  => Ox3
       | 4  => Ox4
       | 5  => Ox5
       | 6  => Ox6
       | 7  => Ox7
       | 8  => Ox8
       | 9  => Ox9
       | 10 => OxA
       | 11 => OxB
       | 12 => OxC
       | 13 => OxD
       | 14 => OxE
       | 15 => OxF
       | _  => Ox0
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
(*
Require Import Verse.PrettyPrint.
Instance pretty_print (n : nat) : PrettyPrint (Vector.t Nibble n) :=
  { doc := fun v => text (Internal.toString v) }.
*)
Definition toN {n} : Vector.t Nibble n -> N :=
  (let fldr := fun m x =>  16 * m + Internal.nibbleToN x in
  Vector.fold_left fldr 0)%N.

Fixpoint fromN l n : Vector.t Nibble l :=
  let (np,r) := N.div_eucl n 16 in
  match l with
  | 0%nat    => []
  | S lp   => Vector.shiftin (Internal.NToNibble r) (fromN lp np)
  end.

Definition fromNat l n := fromN l (N_of_nat n).

Arguments fromN [l] _.
Arguments fromNat [l] _.
