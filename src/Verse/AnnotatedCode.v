Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Ast.
Require Scope.
Require Import Verse.Monoid.
Require Import Verse.AbstractMachine.
Require Import Verse.HlistMachine.

Require Import List.
Import List.ListNotations.

Section AnnotatedCode.

  Variable tyD : typeDenote verse_type_system.

  Definition Str v := Variables.renaming v (Variables.sigParam tyD).
  Definition ann v := StoreP (Str v) -> Prop.

  Inductive line (v : Variables.U verse_type_system) :=
  | inst      : statement v -> line v
  | annot     : ann v -> line v
  .

  Definition lines v := list (line v).

  Definition lineDenote [sc] (l : line (memV sc))
    : mline (memV sc) tyD (HlistMem sc tyD)
    := match l with
       | inst _ s   => justInst (Internals.denoteStmt _ _ _ _ s)
       | annot _ a => justAssert (fun sp => a ((val (fst sp), val (snd sp)) : Pair _))
       end.

  Definition linesDenote [sc] (ls : lines (memV sc))
    := mapMconcat (@lineDenote _) ls.

  Definition codeDenote sc (ls : forall v, Scope.scoped v sc (lines v))
    : mline (memV sc) tyD (HlistMem sc tyD)
    := let sls := fillMemV ls in linesDenote sls.

End AnnotatedCode.

Arguments inst [tyD v].
Arguments annot [tyD v].
Arguments lineDenote [tyD sc].
Arguments linesDenote [tyD sc].
Arguments codeDenote [tyD sc].


Notation "'CODE' c" := (List.map (@inst _ _) c) (at level 59).
(* Notations for annotations *)

Notation "'OLDVAL' v" := (fst (oldAndNew (str := Str _ _)) _ v) (at level 50).
(* TODO - VAL level has to be changed to be stronger than that of '='
          and of b itvector arithmetic notations *)
Notation "'VAL' v" := (snd (oldAndNew (str := Str _ _)) _ v) (at level 50).

Notation "'ASSERT' P" := (inline (fun _ : StoreP (Str _ _) => P)) (at level 100).

Require Import Verse.Scope.
Section CodeGen.

  Variable n : nat.
  Variable sc : Scope.type verse_type_system.

  Variable tyD : typeDenote verse_type_system.

  Variable ac : forall v, Scope.scoped v sc (lines tyD v).

  Definition cp := codeDenote ac.

  (* We allow `getProp` to take a precondition to prefix to the
     extracted Prop. This is never exposed to the user, but is used in
     the CoarseAxiom to provide the proof of the procedure call
     specification to the main body proof.
   *)

  Definition getProp (pc : _ -> Prop)
             (ml : @mline _ (memV sc) tyD (HlistMem _ _))
    := forall (st : str), pc st
                          ->
                          let (i,a) := ml in
                          a (st, st).

  Definition tpt := getProp (fun _ => True) cp.
(*
  Definition getProp (ml : @mline _ (Scope.scopeVar sc) tyD)
    := forall (st : str), snd (ml (scopeStore _ _))
                              ({| store := st |}, {| store := st |}).

  Definition tpt := getProp cp.
*)
End CodeGen.

Global Hint Unfold tpt : Wrapper.
Global Hint Unfold cp  : Wrapper.

Arguments cp sc [tyD].
Arguments getProp [sc tyD].
Arguments tpt sc [tyD].

(* Extracting Prop object from annotated code *)

Ltac getProp func
  := (let cv := constr:(fun v => curry_vec (func v)) in
      let level0 := constr:(Scope.Cookup.specialise cv) in
      let level0break := (eval hnf in (Scope.inferNesting level0)) in
      let pvs := constr:(fst level0break) in
      let level1 := constr:(snd level0break) in
      let lvs := (eval hnf in (fst (Scope.inferNesting level1))) in
      exact (tpt (pvs ++ lvs)%list cv)).

(** * Language Semantics.

Language semantics is now by translating programs to instructions of
the abstract machine. In our case, we have a family of languages that
are parameterised by the underlying type system.  Any member in this
associated with a structure [ts : typeSystem]. To give meanings to
straight line programs in that language, we only need to specify how
the types in that language is mapped into the types of the abstract
machine system. In other words, all we need is a type translator from
the source language to the [abstract_type_system].

 *)

Require Import Verse.Language.Types.

(* ** Semantics for the Verse language.

In the case of the verse language (i.e where our type system is the
[verse_type_system]), we need to only specify the translation for the
[word n] type. We use the [fromWordDenote] function to convert it to
an element of [typeDenote verse_type_system] giving semantics for the
verse language. We define this function inside a section to manage the
verbosity of the types.

*)

Require Import PeanoNat.

Section WordTypeDenote.

  (** We need to give three things to get a [typeDenote
     verse_type_system]

     - A function [wordOfSize] which gives the type associated to the
        verse type [word n],

     - A [const] function which for every [n] gives a way to convert
        the verse constant of type [word n] to [wordOfSize n],

     - A [oper] function that interprets verse operators for [wordOfSize n].

  *)

  Variable wordOfSize : nat -> Type.
  Variable const      : forall sz, constOf verse_type_system (word sz) -> wordOfSize sz.
  Variable oper       : forall sz arity, op arity -> nary (wordOfSize sz) arity.

  Fixpoint typeConv k (ty : type k)  : typeOf abstract_type_system k :=
    match ty with
    | word sz => wordOfSize sz
    | multiword m sz => Vector.t (wordOfSize sz) (2^m)
    | array b e ty  => Vector.t (typeConv direct ty) b
    end.

  Definition constConv (ty : type direct)
    :  constOf verse_type_system ty  -> typeConv direct ty
    := match
        ty as ty0 in (type k)
        return
        (match k as x return (type x -> Type) with
         | direct => fun t : type direct => constOf verse_type_system t -> typeConv direct t
         | memory => fun _ : type memory => IDProp
         end ty0)
      with
      | word n => const n
      | multiword m n => Vector.map (const n)
      | array _ _ _ => idProp
      end.

  Definition vectorApp {A B}{n}(fvec : Vector.t (A -> B) n) (vec : Vector.t A n) : Vector.t B n
    := Vector.map2 (fun f x => f x) fvec vec.
  Fixpoint appN {T} {m} arity : Vector.t (nary T arity) m ->  nary (Vector.t T m) arity
    := match arity with
       | 0 => fun x => x
       | S r => fun fvec vec => appN r (vectorApp fvec vec)
       end.

  Fixpoint opConvGen {k} (ty : type k) arity (o : op arity)
    : nary (typeConv k ty) arity
    := match ty as ty0 in type k0
             return  nary (typeConv k0 ty0) arity
       with
       | word sz =>  oper sz arity o
       | multiword m sz  =>
         appN  arity (Vector.const (oper sz arity o) (2^m))
       | array b e ty0 => appN arity (Vector.const (opConvGen ty0 arity o) b)
       end.
  Definition opConv := @opConvGen direct.

  Definition fromWordDenote :  typeDenote verse_type_system :=
    {| typeTrans  := typeConv;
       constTrans := constConv;
       opTrans    := opConv;
       arrayCompatibility := fun _ _ _ => eq_refl
    |}.
End WordTypeDenote.
