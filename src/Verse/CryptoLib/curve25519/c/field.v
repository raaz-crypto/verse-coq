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
      Definition fullStore p l :=
        match p with
        | 0  => [verse| W := L |] (* First bits to the current word *)
        | _ =>  [verse| W |= `bitsTo p l L` |] (* Not the first bits so OR it *)
        end.


      Definition lowerLoad n  := [verse| L := `toTopBits n W` |].
      Definition lowerStore n := [verse| W |= L ≪ `64 - n` |].


      Definition upperLoad n  :=
        let lBits := len j - n  in (* already has bits from the previous word *)
        [verse| L |= `keepOnlyLower n W` ≪ lBits |].

      Definition upperStore n:= [verse| W := `toTopBits n L` |].

      Definition toLoad (tr : Transfer) : statement progvar :=
        match tr with
        | FullT p l => fullLoad p l
        | LowerT n  => lowerLoad n
        | UpperT n  => upperLoad n
        end.

      Definition toStore (tr : Transfer) : statement progvar :=
        match tr with
        | FullT p l => fullStore p l
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
    unfold Internal.L;
    unfold Internal.W;
    simpl.
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
    dumpgoal.
Abort.

(* end hide *)
