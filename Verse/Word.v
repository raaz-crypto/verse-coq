(* begin hide *)
Require Import Bvector.
Require Import Verse.Error.
Require Import Vector.
Require Import Coq.ZArith.Zdigits.
Require Import BinNums.
Require Import BigNumPrelude.
Require Import String.
Require Import Ascii.
Require Import Verse.PrettyPrint.

(** * Words.

We give an implementation of n-bit words that is useful in to capture
the meanings of

*)


Open Scope Z_scope.
Inductive t (n : nat) : Type :=
| bits : Bvector n -> t n.

Arguments bits [n] _.

Arguments nil [A].


Definition toZ {n}(x : t n) :=
  match x with
  | bits bv => binary_value n bv
  end.

Open Scope string_scope.

Definition bitsToHex {n} (x : t n) : string :=
  let 'bits bv := x in
  let bv' := rev_append_tail bv nil in
  (fix vth {n} (v : Bvector n) : string :=
  match v with
  | false :: false :: false :: false :: vt => vth vt ++ "0"
  | true :: false :: false :: false :: vt  => vth vt ++ "1"
  | false :: true :: false :: false :: vt  => vth vt ++ "2"
  | true :: true :: false :: false :: vt   => vth vt ++ "3"
  | false :: false :: true :: false :: vt  => vth vt ++ "4"
  | true :: false :: true :: false :: vt   => vth vt ++ "5"
  | false :: true :: true :: false :: vt   => vth vt ++ "6"
  | true :: true :: true :: false :: vt    => vth vt ++ "7"
  | false :: false :: false :: true :: vt  => vth vt ++ "8"
  | true :: false :: false :: true :: vt   => vth vt ++ "9"
  | false :: true :: false :: true :: vt   => vth vt ++ "a"
  | true :: true :: false :: true :: vt    => vth vt ++ "b"
  | false :: false :: true :: true :: vt   => vth vt ++ "c"
  | true :: false :: true :: true :: vt    => vth vt ++ "d"
  | false :: true :: true :: true :: vt    => vth vt ++ "e"
  | true :: true :: true :: true :: vt     => vth vt ++ "f"
  | false :: false :: false :: nil         => "x0"
  | true :: false :: false :: nil          => "x1"
  | false :: true :: false :: nil          => "x2"
  | true :: true :: false :: nil           => "x3"
  | false :: false :: true :: nil          => "x4"
  | true :: false :: true :: nil           => "x5"
  | false :: true :: true :: nil           => "x6"
  | true :: true :: true :: nil            => "x7"
  | false :: false :: nil                  => "x0"
  | true :: false :: nil                   => "x1"
  | false :: true :: nil                   => "x2"
  | true :: true :: nil                    => "x3"
  | false :: nil                           => "x0"
  | true :: nil                            => "x1"
  | nil                                    => "x"
  end) _ bv'.

(* Encodings of constants *)
Inductive EncodeError : Prop := BadBase16 | BadBinary | TooFewDigits | TooManyDigits.

Module Base16.


  Open Scope string_scope.
  Open Scope char_scope.


    Definition hexDigit (c : ascii) : Z + {EncodeError}:=
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
     end)%Z.

    Fixpoint hexToZP (sofar : Z) (s : string) :=
      let update := (fun x => sofar * 16 + x)%Z in
      match s with
      | String c sp => x <- update <$> hexDigit c ;  hexToZP x sp
      | EmptyString => inleft sofar
      end.


    Definition hexToZ (n : nat)(s : string) : t n + {EncodeError}
      := match Nat.compare n (4 * String.length s) with
         | Eq => @bits n <$> (Z_to_binary n <$> hexToZP (0%Z) s)
         | Lt => inright TooManyDigits
         | Gt => inright TooFewDigits
         end.

    Definition lastHexDigit z :=
      match binary_value 4 (Z_to_binary 4 z) with
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
               
               
               
      
    Fixpoint ZToHex (n : nat)(z : Z) : string :=
      match n with
      | 0%nat             => EmptyString
      | (S (S (S (S m)))) => ZToHex m (z / 16) ++ String (lastHexDigit z) EmptyString
      | _                 => String (lastHexDigit z) EmptyString
      end.

End Base16.

Definition Ox s := recover (Base16.hexToZ (4 * String.length s) s).

Definition hex {n} (u : t n) :=
  match u with
  | bits bv => Base16.ZToHex n (binary_value n bv)
  end.


(** This function lifts a numeric binary function  to WORDS *)
Definition numBinOp {n} f  (x y : t n) : t n :=
  match x, y with
  | bits xv, bits yv => bits (Z_to_binary n (f (binary_value n xv)(binary_value n yv)))
  end.

(** This function lifts a numeric unary function to WORDS *)
Definition numUnaryOp {n : nat} f (x : t n) : t n :=
  match x with
  | bits xv => bits (Z_to_binary n (f (binary_value n xv)))
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
