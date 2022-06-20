(* begin hide *)
Require Import Arith.
Require Import Verse.
(* end hide *)
(** * Field arithmetic over GF(2²⁵⁵ - 19).


In this module, we implement the field arithmetic over the base field
𝔽 = GF(2²⁵⁵ - 19). we start with considering the representation of
elements of this field.


 *)


(** ** Representing elements.


There are two possible representations of elements in this field

* The packed representation as a 255 bit little endian quantity
  represented as 32 bytes. We consider this as 4 -64-bit little endian
  values.

* The computational representation: Consider the 255 bit number in
  base 2⁵¹ as α = x₀ + x₁ 2⁵¹ .... + x₅ 2²⁰⁴. Each of the xᵢ's
  themselves can be considered as aᵢ + bᵢ 2²⁶.


The packed representation is the standard representation and is in
particular used to storing and transmitting values of the latter and
is thus canonical.  The computational representation should be treated
as an implementation dependent internal format and is designed to make
the implementation of the field operation efficient.

 *)


Definition pos (i : nat) :=
  let j := i / 2 in
  let k := i mod 2 in
  j * 51 + k * 26.

Definition len (i : nat) := pos (S i) - pos i.

Definition nLimbs := 10.
Definition nWord  := 4.

Definition foreachLimb {A : Type}(f : forall i, i < nLimbs -> list A) : list A := iterate f.
Definition foreachWord {A : Type}(f : forall i, i < nWord  -> list A) : list A := iterate f.

Definition Packed := Array 4 littleE Word64.
(** Field element *)
Definition fe (v : VariableT) := Vector.t (v of type Word64) 10.

(* begin hide *)
(* NOTE: These are inline tests *)
Definition bitSizes := foreachLimb (fun i _  => [len i] ).
(* Make sure that all the 255 bits are distributed some where among the limbs. *)
Goal List.list_sum bitSizes = 255.
  trivial.
Qed.

(* end hide *)

Module Internal.

  Inductive Transfer :=
  | FullT  : nat -> nat -> Transfer
  | LowerT : nat -> Transfer
  | UpperT : nat -> Transfer.


  Definition transferSize (t : Transfer) :=
    match t with
    | FullT _ l | LowerT l | UpperT l => l
    end.

  Section Transfer.
    (* The entire limb comes from this word *)

    Context (i j : nat).

    Definition this := i * 64.
    Definition next := S i * 64.


    Definition thisL := pos j.
    Definition nextL := pos (S j).
    Definition endL  := nextL - 1.

    Definition inRangeB m : bool :=
       (this <=? m) && (m <? next).

    Definition fullTB  : bool := inRangeB thisL && inRangeB endL.
    Definition lowerTB : bool := inRangeB thisL && negb (inRangeB endL).
    Definition upperTB : bool := negb (inRangeB thisL) && inRangeB endL.

    Definition transfer : option Transfer :=
      (if inRangeB thisL && inRangeB endL then Some (FullT (thisL - this) (len j))
       else if inRangeB thisL then Some (LowerT (next - thisL))
            else if inRangeB endL then Some (UpperT (nextL - this))
                 else None)%bool.

    Definition toList {A}( oa : option A ) : list A :=
      match oa with
      | Some x => [x]
      | None   => []
      end.
  End Transfer.

  (* begin hide *)
  Definition allLoads (i : nat) := foreachLimb (fun j _  => toList (transfer i j)).

  Definition trSizes (i : nat) := List.list_sum (List.map transferSize (allLoads i)).

  Goal trSizes 0 = 64 /\ trSizes 1 = 64 /\
    trSizes 2 = 64.
    compute. intuition.
  Qed.

  Goal List.list_sum (foreachWord (fun i _ => [trSizes i])) = 255.
    compute.
    trivial.
  Qed.
  (* end hide *)

  Section Load.
    Context {progvar : VariableT}.
    Context (packed : progvar of type Packed).
    Context (temp : progvar of type Word64).
    Context (x : fe progvar).

    Program Definition load (i j : nat)(_ : j < nLimbs) : code progvar :=
      let trTo tr := match tr with
                     | FullT p l => [verse| x[j] := `bitsAt p l temp` |]
                     | LowerT n  => [verse| x[j] := `toTopBits n temp` |]
                     | UpperT n  => let lBits := len j - n in
                                   [verse| x[j] |= `keepOnlyLower n temp` ≪ lBits |]
                     end in
      match transfer i j  with
      | Some tr => [trTo tr]
      | None => []
      end.

    Program Definition store (i j : nat)(_ : j < nLimbs) : code progvar :=
      let xj := [verse| x[j] |] in
      let trTo tr := match tr with
                     | FullT p l => if p =? 0 then [verse| temp := xj |]
                                   else [verse| temp |= `bitsTo p l xj` |]
                     | LowerT n => [verse| temp |= x[j] ≪ `64 - n`  |]
                     | UpperT n => [verse| temp := `toTopBits n xj` |]
                     end
      in match transfer i j with
         | Some tr => [trTo tr]
         | None    => []
         end.

    Program Definition loadAll : code progvar := foreachWord (fun i _ =>
                                                                [code| temp := packed [ i ] |] ++
                                                                  foreachLimb (load i)
                                                   )%list.
    Program Definition storeAll : code progvar := foreachWord (fun i _ =>
                                                                 foreachLimb (store i) ++
                                                                   [code| packed[i] := temp |]
                                                    )%list.
  End Load.


End Internal.

(* begin hide *)


Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.


Axiom MyVar :VariableT.
Axiom P : MyVar of type Packed.
Axiom T : MyVar of type Word64.
Axiom X : fe MyVar.
Goal to_print (Internal.loadAll P T X ).
  unfold Internal.loadAll;
  unfold foreachWord;
  unfold iterate;
    unfold foreach;
  simpl;
    unfold bitsAt; unfold len; simpl;
    unfold keepOnlyLower; simpl;
    unfold keepAt; simpl.
Abort.

Goal to_print (Internal.storeAll P T X).
  unfold Internal.storeAll;
  unfold foreachWord;
  unfold iterate;
    unfold foreach;
  simpl ; unfold len; simpl;
  unfold bitsAt; unfold len; simpl.
Abort.

(* end hide *)
