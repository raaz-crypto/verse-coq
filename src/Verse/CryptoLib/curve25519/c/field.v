(* begin hide *)
Require Import NArith.
Require Import ZArith.
Require Import Arith.
Require Import Verse.
Require setoid_ring.Algebra_syntax.
Require Import Verse.Modular.ModRing.
Require Import Verse.Modular.Equation.
Require Import Psatz.
(* end hide *)
(** * Field arithmetic over GF(2²⁵⁵ - 19).


In this module, we implement the field arithmetic over the base field
𝔽 = GF(2²⁵⁵ - 19). we start with considering the representation of
elements of this field.


 *)

(** The underlying prime *)
Definition P : positive := (2^255 - 19)%positive.

(** The underlying Galois field *)
Definition GF := Zmod P.

(** ** Representing elements.


There are two possible representations of elements in this field

* The _packed representation_ as a 255 bit little endian quantity
  represented as 32 bytes. We consider this as 4 -64-bit little endian
  values.

* The _computational representation_: Consider the 255 bit number in
  base 2⁵¹ as α = x₀ + x₁ 2⁵¹ .... + x₅ 2²⁰⁴. Each of the xᵢ's
  themselves can be considered as aᵢ + bᵢ 2²⁶.

* The _intermediate computational form_ is essentially the
  computational representation with a looser bound on the bit size of
  the last limb: the last limb can have 26 significant bits, i.e. 1
  more than its designated 25 bits. Every arithmetic operation is
  designed to work correctly for such inputs and generate output in
  this intermediate computational form.


The packed representation is the standard representation and is in
particular used to storing and transmitting values and is thus
canonical.  The computational representation should be treated as an
implementation dependent internal format and is designed to make the
implementation of the field operation efficient.

The computational representation given by specifying the bit position
of the [i]-th limb which is given by the function [pos i = ⌈25.5 i⌉]
for the natural number [i]. We also have [posP] and [posN] that works
for limb positions of type [positive] or [N].

In the intermediate computational form, certain field element can have
multiple bit representation. The only point at which we fix this is
just before serialisation. This step will be called the cannonisation
procedure.

 *)

Definition posP (p : positive) :=
  match p with
  | pp~0 => 51 * pp
  | pp~1 => 51 * pp + 26
  | 1 => 26
  end%positive.

Definition posN (n : N) :=
  match n with
  | N0 => 0%N
  | Npos p => Npos (posP p)
  end.


Definition pos (n : nat) := N.to_nat (posN (N.of_nat n)).
Definition len (i : nat) := N.to_nat (let iN := N.of_nat i in
                                    posN (iN + 1) - posN iN)%N.

Definition nLimbs := 10.
Definition nWord  := 4.

Definition foreachLimb {A : Type}(f : forall i, i < nLimbs -> list A) : list A := iterate f.
Definition foreachWord {A : Type}(f : forall i, i < nWord  -> list A) : list A := iterate f.

Definition Packed := Array 4 hostE Word64.

(** Field element in computational representation *)
Definition fe := Vector.t (const Word64) nLimbs.
Require Import Verse.NFacts.

Create HintDb localdb.
Hint Rewrite N.mod_1_r N.sub_0_r : localdb.
Hint Rewrite
  div_mod_sub
  divide_add_mod_multiple
  divide_mod_mod
  add_sub_le : localdb.

(** We now give helper functions to create field element constants. *)
Section FieldElements.

  Import List.ListNotations.
  Definition limbOf (i : N) (n : N) : N :=
    (n  mod (2^posN (i + 1)))/ 2^posN i.

  Definition limbsOf (n : N) : list N :=
    (foreachLimb (fun i _ => [limbOf (N.of_nat i) n ] %list )).


  Definition of_limbs (l : list N) : N :=
    let fld  (acc : N * N) n :=
      let (i , alpha) := acc in
      let incr  :=  (n * 2^(posN i))%N in
      ((i+1),  alpha + incr)%N
    in
    snd (List.fold_left fld l (0%N, 0%N)).



  Ltac local_crush := repeat (match goal with
                              | [ |- (?X | ?Y)%N  ] => eexists (Y/X)%N; compute; trivial
                              | [ |- _ <> _  ] => compute;
                                               let H := fresh "Hyp" in
                                               intro H; inversion H
                              | [ |- (_ mod _ <= _ mod _)%N ] => apply divide_mod_le
                              | [ |- ( _ mod _ < _)%N      ] => apply N.mod_lt
                              | [ |- (_ < _)%N ] => lia
                              | _ =>  autounfold with localdb; simpl; autorewrite with localdb; trivial
                              end).

  Hint Unfold limbsOf of_limbs limbOf : localdb.
  Lemma limb_spec : forall n, of_limbs (limbsOf n) = (n mod 2^255)%N.
    intro.
    local_crush.
  Qed.


  Definition limbsOfGF (alpha : GF) : list N := limbsOf (to_N alpha).
  Definition GF_of_limbs (l : list N) : GF := of_N (of_limbs l).

  Lemma modPLt255 : forall n : N, (n mod (Npos P) < 2^255)%N.
    intro n.
    apply (N.lt_trans _ (Npos P)); local_crush; compute; trivial.
  Qed.

  Hint Resolve modPLt255 : localdb.


  Import setoid_ring.Algebra_syntax.
  Hint Unfold
         equality
         eq_Zmod
         eqZmod
         eqMod
         limbsOfGF
         GF_of_limbs
    : localdb.

  Hint Rewrite to_vs_of_N_spec : localdb.
  Lemma limbsOfGF_spec : forall alpha : GF, GF_of_limbs (limbsOfGF alpha) == alpha.
    intros.
    destruct alpha;
      unfold GF_of_limbs;
      unfold limbsOfGF;
    rewrite to_vs_of_N_spec;
    rewrite limb_spec.
    assert (Hyp: (((n mod N.pos P) mod 2^255) = n mod N.pos P)%N).
    apply N.mod_small; eauto with localdb.
    rewrite Hyp.
    local_crush.
  Qed.

  Definition wordsOf  (alpha : GF) := List.map (NToConst Word64) (limbsOfGF alpha).
  Definition of_Words (vec : fe) : GF := of_N (of_limbs (List.map (@Bv2N 64) (Vector.to_list vec))).
  Definition GF2const (alpha : GF) : fe :=  Vector.of_list (wordsOf alpha).
  Arguments GF2const (alpha)%modular.


  Definition feOne         : fe := GF2const 1.
  Definition feZero        : fe := GF2const 0.
  Definition minus18_const : fe := GF2const ( -18 ).
  Definition minus19_const : fe := GF2const ( -19 ).

  Lemma minus18_const_specs : of_Words minus18_const == -18%modular.
    compute; trivial.
  Qed.

  Lemma minus19_const_specs:  of_Words  minus19_const == -19%modular.
    compute; trivial.
  Qed.



End FieldElements.

(** A variable vector that can hold a field element. For the purpose
    of this implementation, you should think of [feVar] as a variable
    that can hold a field element computational representation *)

Definition feVar (v : VariableT) := Vector.t (v of type Word64) nLimbs.

Program Definition copyFeVar {progvar}(u v : feVar progvar) : code progvar :=
  foreachLimb (fun i _ => [code| u[i] := v[i]|]).


Program Definition setFeVar {progvar}(u : feVar progvar)(alpha : fe) : code progvar :=
  foreachLimb(fun i _ => [code| u[i] := alpha[i] |]).

(* begin hide *)
(* NOTE: These are inline tests *)
Definition bitSizes := foreachLimb (fun i _  => [len i] ).
(* Make sure that all the 255 bits are distributed some where among the limbs. *)
Goal List.list_sum bitSizes = 255.
  trivial.
Qed.

(* end hide *)

Module Internal.

  (** One could generate the instructions for load and store directly,
      however we do it in two steps so that we can prove (more like
      test) some of the basic functions here.

      In the packed form, the bits are treated as 4 × little endian
      64bit quantities which amounts to 256 bits of which only 255
      bits are actually relevant when it comes to reduced from. In the
      computation representation, each limb is either 25 or 26
      bits. For each limb xⱼ, we have the following situations
      (mutually exclusive situations)

      * all the bits of xⱼ are within some word wᵢ

      * The bits of xⱼ are split across two consecutive words wᵢ and
        wᵢ₊₁ in which case the lower bits xⱼ come from (the higher
        bits of) wᵢ and the higher bits of xⱼ come from (the lower
        bits of) wᵢ₊₁

        We define an auxiliary data which gives the transfer
        instructions between the ith word wᵢ and jth limb xⱼ. The
        constructors are

        * [FullT pos len]: all [len] bits of the limb come from the
        the given word starting at position [pos]

        * [Lower n]: The lower [n] bits of the limb comes from the upper [n] bits
        of the word.

        * [Upper n]: The upper [n] bits of the limb comes from the upper [l] bits

  *)
  Inductive Transfer :=
  | FullT  : nat -> nat -> Transfer
  | LowerT : nat -> Transfer
  | UpperT : nat -> Transfer.


  (** This computes the transfer size associated to a single transfer instruction *)
  Definition transferSize (t : Transfer) :=
    match t with
    | FullT _ l | LowerT l | UpperT l => l
    end.

  (** Computing the transfer between wᵢ and xⱼ *)
  Section Transfer.
    (* The entire limb comes from this word *)
    Context (i j : nat).

    (** Starting bit positions of the wᵢ and wᵢ₊₁ *)
    Definition this := i * 64.
    Definition next := S i * 64.


    (** Starting bit positions of xⱼ and xⱼ₊₁ *)
    Definition thisL := pos j.
    Definition nextL := pos (S j).
    Definition endL  := nextL - 1.  (** ending bit position of xⱼ *)

    (** Checks whether a given bit position is within the range of wᵢ *)
    Definition inRangeB m : bool :=
       (this <=? m) && (m <? next).

    (** Compute the transfer instruction associated with wᵢ and
        xⱼ. The result is optional as it is possible that none of the
        bits of xⱼ is from wᵢ.  *)
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
  (* We now prove some small properties of the transfer instructions thus computed *)
  Definition allLoads (i : nat) := foreachLimb (fun j _  => toList (transfer i j)).

  Definition trSizes (i : nat) := List.list_sum (List.map transferSize (allLoads i)).

  Goal trSizes 0 = 64 /\ trSizes 1 = 64 /\
    trSizes 2 = 64 /\ trSizes 3 = 63.
    compute. intuition.
  Qed.

  Goal List.list_sum (foreachWord (fun i _ => [trSizes i])) = 255.
    compute.
    trivial.
  Qed.
  (* end hide *)

  (** We now generate the actual verse instruction from the transfer instructions *)
  Section InstructionGenerate.
    Context {progvar : VariableT}.
    Context (word    : progvar of type Packed).
    Context (limb    : feVar progvar).

    (** The instructions to load appropriate bits into the jth
       limb. We assume that the ith word is already loaded into the
       word [w].
     *)

    Section ForEachIJ.
      (* We assume that all loads happen from lower bits (and
         therefore lower words) to upper words. Also the ith word is
         available in the temporary word [w] *)

      Context (i : nat)`(i < nWord).
      Context (j : nat)`(j < nLimbs).
      Program Definition  W    := [verse| word[i] |].
      Program Definition  L := [verse| limb[j] |].

      Definition fullLoad p l   := [verse| L := `bitsAt p l W` |].
      Definition fullStore (p : nat) :=
        match p with
        | 0  => [verse| W := L      |] (* First bits to the current word *)
        | _ =>  [verse| W |=  L ≪ p |] (* Not the first bits so OR it *)
        end.


      Definition lowerLoad n  := [verse| L := `toTopBits n W` |].
      Definition lowerStore n := [verse| W |= L ≪ `64 - n` |].


      Definition upperLoad n  :=
        let lBits := len j - n  in (* already has bits from the previous word *)
        [verse| L |= `keepOnlyLower n W` ≪ lBits |].

      Definition upperStore n := let lowerBits := len j - n in
        [verse| W := L ≫ lowerBits |].

      Definition toLoad (tr : Transfer) : statement progvar :=
        match tr with
        | FullT p l => fullLoad p l
        | LowerT n  => lowerLoad n
        | UpperT n  => upperLoad n
        end.

      Definition toStore (tr : Transfer) : statement progvar :=
        match tr with
        | FullT p l => fullStore p
        | LowerT n  => lowerStore n
        | UpperT n  => upperStore n
        end.

      Definition load  := toList (option_map toLoad (transfer i j)).
      Definition store := toList (option_map toStore (transfer i j)).
    End ForEachIJ.

    Definition loadAll  := foreachWord (fun i pf => foreachLimb (load  i pf)).
    Definition storeAll := foreachWord (fun i pf => foreachLimb (store i pf)).

  End InstructionGenerate.

End Internal.

(* begin hide *)

(* Just to display stuff for easy visualisation *)
Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.


Axiom MyVar :VariableT.
Axiom W : MyVar of type Packed.
Axiom T : MyVar of type Word64.
Axiom L : feVar MyVar.
Goal to_print (Internal.loadAll W L ).
  unfold Internal.loadAll;
    unfold foreachWord;
    unfold foreachLimb;
    unfold iterate;
    unfold foreach; simpl;
  unfold Internal.fullLoad;
    unfold Internal.lowerLoad;
    unfold Internal.upperLoad;
    unfold len;
    unfold bitsAt;
    unfold Internal.L;
    unfold Internal.W;
    simpl;
    idtac "Loading of field elements:";
    dumpgoal.

Abort.

Goal to_print (Internal.storeAll W L).
  unfold Internal.storeAll;
    unfold foreachWord;
    unfold iterate;
    unfold foreach; simpl;
    unfold Internal.fullStore;
    unfold Internal.lowerStore;
    unfold Internal.upperStore;
    unfold len;
    unfold Internal.W;
    unfold Internal.L;
    simpl;
    idtac "Storing of field elements:";
    dumpgoal.
Abort.

(* end hide *)

(** * Carry propagation.

During arithmetic operations, limbs can contain more that their
designated number of bits. In such cases we propagate the bits the
next limb (cycling when we reach the last limb *)



Section CarryPropagation.

  Context {progvar : VariableT}.
  Context (limb : feVar progvar).
  Program Definition carryFrom (i : nat)(_ : i < nLimbs) :=
    if (i =? 9) then [verse| `19` * (limb[9] ≫ `len 9`) |]
    else [verse| limb[ i ]  ≫ `len i` |].

  Definition trimLimb (i : nat)(_ : i < nLimbs) : code progvar.
    verse ([keepOnlyLowerUpdate (len i) [verse| limb[ (i+nLimbs - 1) mod nLimbs] |]]).
  Defined.
  Definition propagateTo (i : nat)`(i < nLimbs) : code progvar.
    verse ( [code| limb[i] += carryFrom[ (i + nLimbs - 1) mod nLimbs ]
            |] ++ (trimLimb ((i + nLimbs - 1) mod nLimbs) _))%list.
  Defined.

  (* We perform a full cycle of propagation by starting at the highest limb *)
  Definition propagate : code progvar := foreachLimb propagateTo.

End CarryPropagation.

(** * Final modular reduction.


The intermediate computational form represents a number 0 <= α <= 2²⁵⁶
- 1 Let p be the prime 2²⁵⁵ - 19 then we would like to computing an
integer 0 <= α₀ < p such that α₀ = α (mod p). We do this in two stages

1. α is of the form b 2²⁵⁵ + γ for some γ < 2²⁵⁵ - 1 and b is the
   256-th bit of α. A single carry propagation of α gives β <= 2²⁵⁵ -
   1 + 19 such that β such that α = β (mod p).

2. Consider the _reduction amount_ B of β defined as the number
   starting from 256-th bit onwards of of β + 19. Clearly since β <=
   2²⁵⁵ - 1 + 19, β + 19 < 2²⁵⁵ + 38 which is clearly <
   2²⁵⁶. Therefore the reduction amount B cannot be more than 1-bit.

   We claim β + B . 19 (mod 2²⁵⁵) is the desired element. There are
   only two possibilities β < p (in which case B = 0) and p <= β < 2 p
   in which case B = 1.

   - In the first case clearly β + B 19 = β (mod 2²⁵⁵) and hence is
     the desired final form.

   - In the second case β + 19 = γ + 2²⁵⁵ (The 2²⁵⁵ becomes the bit
     B).  Notice that γ = β - (2²⁵⁵ - 19) = β (mod p) and γ < p. is
     the desired element. But γ is just β + B . 19 mode 2²⁵⁵.



 *)

Section FieldReduction.

  Context {progvar : VariableT}.
  Context (x : feVar progvar) (B : progvar of type Word64).
  Program Definition computeReduceBit  : code progvar
    := let stmt i (_ : i < nLimbs) := if i =? 0 then [code| B := x[i] + `19` ; B >>= `len 0` |]
                     else [code| B += x[i] ; B >>= `len i` |]
       in foreachLimb stmt.

  Definition reduce  : code progvar.
    verse(propagate x
      ++ computeReduceBit ++ [code| x[0] += B * `19` |]
      ++ propagate x)%list.
  Defined.

End FieldReduction.

(** ** How many and when ?

Checking whether any of the carry is actually zero is not a good idea
(branching based on secret). So carry propagation has to be done
enough times. For a multi-limb [feVar] like [X], let [size(X)] denote
the size of its largest (in magnitude) limb. Consider an instruction
of the kind A := B ∘ C. To avoid overflow during operations we need
the following restriction.

1. For addition both B and C should have limbs of at-most size 63 for
   no overflow to take placed.

2. For multiplication B and C should have at-most 26 bits in each of
   its limbs. A simple way to ensure this is to get B and C into their
   intermediate computational representation.

3. For subtraction C _should be_ in its intermediate computation
   representation (a mere bound of 26 bits is not enough unlike in the
   case of multiplication). However for the operand B, like addition
   we only need a bound of 62 (subtraction can generate additional
   carry)

The result in A has the following bounds.

1. For addition A is of size at most 1 more than the maximum size of B
   and C.

2. For subtraction A is of size at most 1 more than the
   [max(size(B),26)] and

3. For multiplication which is safe (no overflow), we can assume that
   the size of A is at most 61 bit.

The considerations for carry propagation is as follows.

1. Doing more carry propagation that is required is always safe.

2. For a multi-limb [feVar] [X], a single carry propagation will get
   it to intermediate computation representation if size(X) < 50. For
   64-bit limbs 2 carry propagation is sufficient in any case.

Consider a variable X, we do enough carry propagation based on how it
is used in later instructions. If X is used subsequently as an operand
for a multiplication, or is the negated operand for an instruction,
get it to the intermediate computational form. This may need two carry
propagation in the worst case but one may even get away by a single
operation if we know (from how X is computed), whether size(X) < 50.
If X is used only as additive operand then we can often get away
without any carry propagation on X.


*)

(* begin hide *)
Goal to_print (propagate L).
  unfold propagate.
  unfold foreachLimb;
    unfold iterate;
    unfold foreach;
  simpl; unfold carryFrom; unfold len; simpl;
    idtac "Carry propagation:";
    dumpgoal.
Abort.
(* end hide *)

(** ** Conditional swapping

Given two field elements A , B and a bit b we want to swap the values
in A and B depending on whether the bit is 1. In order to avoid side
channel information we do the swapping by essentially performing (A,
B) := b B + (1 - b) A, b A + (1 - b) B).

 *)

Section Swapping.

  Context {progvar : VariableT}.

  Variable TA  : progvar of type Word64.
  Variable b   : progvar of type Word64.
  Variable A B : feVar progvar.

  Program Definition swap : code progvar :=
    foreachLimb (fun i _ => [code|
                          TA   := A[i];
                          A[i] := b * B[i] + (`1` - b) * A[i];
                          B[i] := b * TA   + (`1` - b) * B[i]
      |]).

End Swapping.


(** * Masks

A mask associated with a bit is a continuation of that bit to the
entire word. For example if the word size is 64-bits, then the mask
associated with the bit b is as the all ones (i.e. 2⁶⁴ - 1) or the all
zeros word depending on whether b is 1 or 0 respectively. Converting
from bits to mask makes some of the operations faster due to the use
of the more efficient bitwise operations instead of the arithmetic
operations.

 *)

Definition mask {progvar : VariableT}{T}`{EXPR progvar Word64 T}(t : T) : expr progvar of type Word64 := [verse| (~t) + `1` |].

Section SwappingEfficient.

  (**
      A more efficient swapping routine that makes use of a swap mask.
      This is more efficient because

      1. It does not need a temporary variable
      2. Instead of 64-bit multiplication it uses the 64 bit bitwise operation.

   *)

  Context {progvar : VariableT}.

  Program Definition swapE (b : progvar of type Word64) (A B : feVar progvar)
    : code progvar :=
    ( foreachLimb (fun i _ =>
                     [code| A[i] := A[i] ⊕ B[i] ;
                      B[i] := (b & (A[i] ⊕ B[i])) | (~b & B[i]) ;
                      A[i] := A[i] ⊕ B[i]
                     |]    ))%list.

End SwappingEfficient.



(** ** Field arithmetic operations.

We implement the following operations for field elements.

1. A := B + C or A += B.

2. A := B - C or A -= B.

2. A := B * C or A *= B.


No explicit propagation is done because as remarked above, the number
of propagations that is to be done depends on the operations that we
are performing and the context.

We start with addition which is more or less straight forward. If we
start with limbs in intermediate computational representation then
after an addition step we will end up with each limb having an
additional bit. A single round of propagation should get it back to
the intermediate computational representation.

Note that one does not need to do a single propagation every time. If
there is a chain of at most 25 additions, we need to do the
propagation only once.

 *)

Section Addition.

  Context {progvar : VariableT}.

  Variable A B C : feVar progvar.

  Program Definition add : code progvar :=
    foreachLimb (fun i _ => [code| A[i] := B[i] + C[i]  |]).
  Program Definition addAssign : code progvar :=
    foreachLimb (fun i _ => [code| A[i] += B[i] |] ).

  Definition addAssignSmall (small : expr progvar of type Word64) : code progvar.
    verse([code| A[0] += small |]).
  Defined.

End Addition.

(** ** Subtraction.

Imagine the 255 bit field element α with its bits distributed among
the 10 limbs. Complementing these 255 bits would mean that we replace
the associated integer with 2²⁵⁵ - 1 - α where as what we do want to
compute is 2²⁵⁵ - 19 - α. So the negation of α is obtained by
complementing and adding the field element -18.

There are two important additional issues.

1. Each limb which has 25 (or 26) bit need to be complemented only on
   those many bits. This also takes care of there being no rounding
   errors when we eventually add this to a field element in
   intermediate form.

2. The field element α, in its intermediate form might have an
   additional bit in its 256 bit position (i.e. α = α₀ + b . 2²⁵⁵ = α₀
   + b . 19) where b = 0/1. The negation α in this case is - α₀ - b
   . 19. Therefore, we need to add an additional (- b . 19) to -α₀.


Other than these adjustments, subtraction is essentially addition.

*)
Section Subtraction.

  Context {progvar : VariableT}.

  (** In the intermediate computation form each field element is
      expressed as a 256 bit constant [b₀],...,[b₂₅₅] of which the bit
      [b₂₅₅] contributes [minus_19] to the computation.  All the code
      in the subtraction section will use this temporary variable to
      get the 256-th bit of the appropriate field element.

   *)
  Variable B255 : progvar of type Word64.

  (** Function to set 256-th bit given a field element
      variable. Notice that, we want this bit to be a mask,
      i.e. [B255] should have all ones if the 256 bit of the field
      element is 1 and 0 otherwise. Thus we can use [B255] as a mask
      to select the appropriate expression.
   *)

  Program Definition setB255 (X : feVar progvar) : code progvar :=
    let x := [verse| X[9] |] in
    ([code| B255 := `toTopBits 26 x`;
            B255 := `mask B255`

    |]).


  (** For a field element if we complement all the bits, we get the
      nat value (2²⁵⁵ - 1 - α) We need to adjust this will additional
      additive terms. Firstly, we need to add the field constant -18
      so that the nat value becomes (2²⁵⁵ - 19 - α). In addition if
      the 256-th bit was 1 in the bit representation, we also need to
      add an additional -19. This we capture with [adjustExpr]

   *)

  Program Definition adjustExpr i (_ : i < nLimbs) : expr progvar of type Word64
      := [verse| `minus18_const` [i] + (B255 & minus19_const [i]) |].

  Program Definition complement (X : feVar progvar) i (_ : i < nLimbs)  : expr progvar of type Word64
    := keepOnlyLower (len i) [verse| ~ X[i] |].

  Program Definition update_complement (X : feVar progvar) i (pf : i < nLimbs) : code progvar :=
    let x := [verse| X[i] |] in
    [code| X[i] := `complement X` [i] |].


  (** Negate the field element in the register A *)
  Program Definition negate (A : feVar progvar) : code progvar:=
    (setB255 A
       ++ foreachLimb (update_complement A)
       ++ foreachLimb (fun i pf => [code| A[i] += adjustExpr[i] |])
    )%list.

  Program Definition sub (A B C : feVar progvar) : code progvar :=
    let CComp := complement C in
    (setB255 C
       ++ foreachLimb (fun i pf => [code| A[i] := B[i] + CComp[i] + adjustExpr[i] |])
       )%list.

  Program Definition subAssign (A B : feVar progvar) : code progvar :=
    let BComp := complement B in
    (setB255 B
       ++ foreachLimb (fun i _ => [code| A[i] += BComp[i] + adjustExpr[i]  |] ))%list.

End Subtraction.


(** ** Multiplication

Given two elements a and b with limbs aᵢ and bⱼ respectively consider
the associated field element [∑ aᵢ 2ᵖᵒˢ ⁱ] and [∑ bⱼ 2ᵖᵒˢ ʲ]. The
product is the sum of terms Tᵢⱼ of the form [aᵢ * bⱼ 2ᵖᵒˢ ⁱ ⁺ ᵖᵒˢ ʲ].
Each of these terms contribute to some limbs, in fact exactly one of
the limbs, in the final product as should be clear from the analysis
below.

For a moment assume that [i + j < 10]. Since [pos i = ⌈25.5 i⌉], we
have [pos (i + j) ≤ pos i + pos j ≤ pos (i + j) + 1]. We make use of
the inequality ⌈x + y⌉ ≤ ⌈x⌉ + ⌈y⌉ ≤ ⌈x + y⌉ + 1. What this means is
that the term Tᵢⱼ contributes only to the limb [i + j] possibly with
an additional multiplicative factor of 2 (when the second part of the
inequality is actually an equality. When [i+j >= 10] then Tᵢⱼ similarly
contributes to the limb [i + j mod 10] with the multiplicative factor
being 19 * 2 (because 2²⁵⁵ = 19 int the field).

*)

Section Multiplication.
  Context {progvar : VariableT}.
  Context (A B C : feVar progvar).


  (** Compute the term Tᵢⱼ suitably scaled *)
  Section Term.
    Context (i : nat)`(i < nLimbs).
    Context (j : nat)`(j < nLimbs).


    Definition multBy (n : nat) (e : expr progvar of type Word64) : list (expr progvar of type Word64) :=
      match n with
       | 0 => []
       | 1 => [e]
       | 2 => [ [verse| e ≪ `1` |] ]
       | 4 => [ [verse| e ≪ `2` |] ]
       | _ => [ [verse| e * `n` |] ]
      end%nat.

    (* If the power is greater than 2²⁵⁵ then we reduce we multiply with 19 instead which *)
    Definition modularFactor : nat :=
      if i + j <? 10 then 1 else 19.

    (* The additional power of 2 that needs to be adjusted for. Recall
       that the term B[i] * C[j] contributs to A[i+j `mod` 10] but
       needs to be adjusted by a factor of 2 if pos i + pos j > pos (i
       + j).

       Recall that pos i = ⌈25.5 i ⌉ therefore for even i pos i = 25.5
       i and for odd i pos i = 25.5 i + 0.5. Doing the case by case
       analysis of i and j we see that pos i + pos j > pos (i + j)
       only when both i and j are odd.

       We could have directly written this condition but that makes code generation
       slower. (alternatively may be we can work with binary nats.
     *)

    Definition shouldAdjust u v : bool:=
      let odd n := n mod 2 =? 1 in
      odd u && odd v.
    Definition adjustFactor : nat :=
      if shouldAdjust i j then 2 else 1.


    Definition oddN (n : N) := exists q, n = (2 * q + 1)%N.

    Definition termFactor : nat := modularFactor * adjustFactor. (* If we use it directly the code generation
                                                              is slower *)

    Program Definition term := multBy termFactor [verse| B[i] * C[j] |].

  (* Code generation is slower here by a factor of 6. So makes sense to avoid this.
     May be there are other faster ways to
     *)

    Definition sqFactor : nat := if i <? j then termFactor * 2
                              else if i =? j then termFactor
                                   else 0.
    Program Definition sqTerm := multBy sqFactor [verse| B[i] * B[j] |].

  End Term.

  (*
  Goal to_print (foreachLimb (fun i pfi => (foreachLimb (fun j pfj => termP i pfi j pfj)))).
    unfold foreachLimb;
    unfold iterate;
      unfold foreach.
    unfold term.
    time simpl.
    (* Tactic call ran for 2.846 secs (2.846u,0.s) (success) *)
    (* Tactic call ran for 13.399 secs (13.398u,0.s) (success) *)
  Abort.

   *)
  (** Compute the terms Tᵢⱼ that contribute for the limb k *)
  Section Update.
    Context (k : nat)`(k < nLimbs).
    Definition termFrom (i : nat)`(i < nLimbs) : list (expr progvar of type Word64).
      refine (term i _ ((k + nLimbs - i)  mod nLimbs) _); verse_crush.
    Defined.

    Definition sqTermFrom (i : nat)`(i < nLimbs) : list (expr progvar of type Word64).
      refine (sqTerm i _ ((k + nLimbs - i)  mod nLimbs) _); verse_crush.
    Defined.

    Definition termsFor := foreachLimb termFrom.
    Definition sqTermFor := foreachLimb sqTermFrom.

    Program Definition update exps : code progvar :=
      match exps with
      | (x :: xs) => [code| A[k] := `List.fold_left (fun e1 e2 => [verse| e1 + e2 |]) xs x` |]
      | _ => []
      end%list.

    Definition multUpdate := update termsFor.
    Definition sqUpdate  := update sqTermFor.
  End Update.

  Definition mult   := foreachLimb multUpdate.
  Definition square := foreachLimb sqUpdate.


  Definition multN (n : N) : code progvar.
    verse (
        match n with
        | 2%N => foreachLimb (fun i _ => [code| A[i] := B[i] << `1` |])
        | 4%N => foreachLimb (fun i _ => [code| A[i] := B[i] << `2` |])
        | _ => foreachLimb (fun i _ => [code| A[i] := B[i] * `n`  |])
        end
      ).
  Defined.

End Multiplication.

Section Inverse.

  (** ** Inverse through powering.

      By Fermat's little theorem we know that aᵖ⁻² . a = aᵖ⁻¹ = 1 mod
      p so aᵖ⁻² is the inverse of a. Therefore we perform inverse of
      [z] by computing the [p-2]-th power of z using the repeated
      squaring method Since this is a known power exponentiation there
      is no side channel here.
*)


  Definition ipower := Npos ((P - 2)%positive).
  Import List.ListNotations.
  (* This is a representation of ipower as bits. We will use this to build our inverse function *)
  Definition ibitsRep : list (repeated bool) := ([repeat 2 true; repeat 1 false; repeat 1 true; repeat 1 false; repeat 250 true])%list.
  (* The actual ibits as a list *)
  Definition ibits  := Repeat.unroll (fun x : bool => [x]%list) ibitsRep.

  (* Ensure that ibitsRep when unrolled gives the value P - 2 as a number *)
  Goal Bv2N (Vector.of_list ibits) = ipower.
    compute; trivial.
  Qed.


(** The process is simple. In each step we will square [z] and keep
    the cumulative product in [cp]. If [cp] started out as 1 then we
    will end with [cp] containing [z⁻¹]. Rather than computing the
    inverse, our application is to compute [a . z⁻¹] for some [a]. In
    such case we can just start the algorithm with [cp] with [a] in
    it instead of 1.
*)


  Context {progvar : VariableT}.
  Context (cP z temp : feVar progvar).


(** There are two additional problems we need to handle

1. Firstly our multiplication and squaring step can only compute the
   result in an [temp] variable. We need to prepare the [z] and [cp]
   for the next step by assigning them back from [temp]

2. We also need to adjust limbs by two carry propagation (as
   multiplication is involved).


We perform the first carry propagation together with the assignment and
then a single propagation.

 *)


  (** The squaring code *)
  Definition sqZ : code progvar :=
    (square temp z
       ++ propagateAssign z temp
       ++ propagate z
    )%list.

  (** Multiplication code *)
  Definition multAndSquare : code progvar :=
    (mult temp cP z
       ++ propagateAssign cP temp
       ++ propagate cP
       ++ sqZ
    )%list.

  Definition updateProd (bit : bool) : code progvar :=
    if bit then multAndSquare else sqZ.


  Definition inverse : Repeat (statement progvar) := List.map (Repeat.map updateProd) ibitsRep.


End Inverse.

(* begin hide *)
Axiom A B C : feVar MyVar.

Goal to_print (mult A B C).
  unfold mult;
  unfold foreachLimb;
    unfold iterate;
    unfold foreach;
    unfold update;
    time simpl;
  unfold termFactor; simpl;
  idtac "Code for multiplication:";
  dumpgoal.
Abort.


Goal to_print (square A B).
  unfold square;
  unfold foreachLimb;
    unfold iterate;
    unfold foreach;
    unfold update;
    time simpl;
    unfold sqFactor;
    unfold termFactor; simpl;
    idtac "Code for squaring:".
  time dumpgoal.
Abort.
