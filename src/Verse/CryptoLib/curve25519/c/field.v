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
Definition fe (v : VariableT) := Vector.t (v of type Word64) nLimbs.

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
    Context (limb    : fe progvar).

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

      Definition load : code progvar := toList (option_map toLoad (transfer i j)).
      Definition store : code progvar := toList (option_map toStore (transfer i j)).
    End ForEachIJ.

    Definition loadAll  : code progvar := foreachWord (fun i pf => foreachLimb (load  i pf)).
    Definition storeAll : code progvar := foreachWord (fun i pf => foreachLimb (store i pf)).

  End InstructionGenerate.

End Internal.

(* begin hide *)

(* Just to display stuff for easy visualisation *)
Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.


Axiom MyVar :VariableT.
Axiom W : MyVar of type Packed.
Axiom T : MyVar of type Word64.
Axiom L : fe MyVar.
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
  Variable limb    : fe progvar.

  Program Definition carryFrom (i : nat)`{i < nLimbs} :=
    if (i =? 9) then [verse| `19` * (limb[9] ≫ `len 9`) |]
    else [verse| limb[ i ]  ≫ `len i` |].


  Definition propagateTo (i : nat)`(i < nLimbs) : code progvar.
    verse ([code| limb[i] += `carryFrom ((i + nLimbs - 1) mod nLimbs)` |]).
  Defined.

  (* We perform a full cycle of propagation by starting at the highest limb *)
  Definition propagate := foreachLimb propagateTo.

End CarryPropagation.


(** ** How many progagations ?

Firstly checking whether any of the carry is actually zero is not such
a good idea (branching based on secret). So the answer is that we run
the propagate one two many times. In the standard representation, we
want to ensure that the ith limb contains [len i] many bits (rest
needs to be propagated further on. We allow for an additional bit at
the top most limb x₉ which will be adjusted after the end of all
operations. Consider the following arithmetic operations

* _Addition:_ Here there is at most one additional bit generated. So
  the carry from xᵢ to xᵢ₊₁ bit. What this means is that if xᵢ₊₁ was
  already of length len (i + 1) at most an additional bit is added to
  it which then is propagated further up.

* _Multiplication:_ If we think of the limbs as forming a polynomial
  over the indeterminate X then the coefficients cₖ (∑ aᵢ Xⁱ)(∑ bᵢ Xʲ)
  will be of the form cₖ = 10 terms of the form aᵢ bⱼ * 2 * 19. Which
  is bounded by 2⁵² * 380 = 2⁶¹ and hence are of 61 bits each.

  Now consider the first round of propagation from c₉ to c₀, c₀ to c₁
  ...  c₈ to c₉.  When we started each cᵢ's had 61 bits at most and
  hence they propagate at most 62 - 25 = 37 bits in each stage. After
  one cycle of propagation c₀ to c₈ have their correct number of bits
  but c₉ is a 25-bit number + a 37 bit number = 38 bit number. What
  this means is in the next round we will be propagating 38 - 25 = 11
  bits from c₉ to c₀ but then on will only be propagating at most 1
  bit; adding a 11-bit carry to a 25 or 26 bit number will result in
  at most have an additional 1 bit carry. As a result after the end of
  the second round of propagation all limbs c₀ ... c₈ will have the
  correct number of bits but c₉ might have one addition bit (i.e 26
  bits instead of 25 bits). Although this is not the standard
  representation, we do not need to perform any further propagation
  until the final result is desired for, with this bit counts, none of
  our arithmetic operations will overflow.

NOTE: Instead of starting from the largest limb, we could start from
any of the limb but then that particular limb will have an additional
bit. It is better to therefore start the propagation from one of the
25 bit making it 26 bit and our 61 bit bound holds.

*)

(* begin hide *)
Goal to_print (propagate L).
  unfold propagate.
  unfold foreachLimb;
    unfold iterate;
    unfold foreach.
  simpl; unfold carryFrom; unfold len; simpl.
    idtac "Carry propagation:";
    dumpgoal.
Abort.
(* end hide *)
