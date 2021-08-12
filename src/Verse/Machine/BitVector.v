(** * Bit vector semantics.

This module exposes a semantics that is based on interpreting the
words as bitvectors.

*)

Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.AbstractMachine.
Require Import Verse.BitVector.

Definition wordOfSize : nat -> Type := Types.BWord.
Definition const : forall sz : nat, constOf verse_type_system (word sz) -> wordOfSize sz
  := fun sz x => x.

Definition oper (sz arity : nat) (o : op arity)
  := match o in op arity0 return nary (wordOfSize sz) arity0 with
     | plus      => @BVplus    _
     | minus     => @BVminus   _
     | mul       => @BVmul     _
     | quot      => @BVquot    _
     | rem       => @BVrem     _
     | bitOr     => @BVor      _
     | bitAnd    => @BVand     _
     | bitXor    => @BVxor     _
     | bitComp   => @BVcomp    _
     | shiftL  n => @BVshiftL  _ n
     | shiftR  n => @BVshiftR  _ n
     | rotL    n => @BVrotL    _ n
     | rotR    n => @BVrotR    _ n
     end.

Definition bvDenote : typeDenote verse_type_system := fromWordDenote wordOfSize const oper.

(* TODO : While the following two tactics are fairly generic, they
          don't work without specific BitVector functions. Needs to be
          organized better.
 *)


(** Tactics for proof goal presentation *)

Require Import Verse.BitVector.ArithRing.

(* Destruct the variable store for easier access to valuations *)

Module HProdn.

  Fixpoint t [T n] (u : T -> Type)
  : Vector.t T n -> Type
    := match n as n0 return Vector.t _ n0 -> Type with
       | 0   => fun _  => unit
       | S m => fun v0 => (u (Vector.hd v0) * t u (Vector.tl v0))%type
       end.

End HProdn.

Fixpoint lamn ts v n (sc : Scope.type ts n)
  : (HProdn.t v sc -> Type) -> Type
  := match n as n0
           return
           forall sc0 : Scope.type _ n0,
             (HProdn.t v sc0 -> Type) -> Type with
     | 0   => fun _ f => forall t, f t
     | S n => fun _ f => forall t , lamn _ _ n _ (fun x => f (t, x))
     end sc.

Lemma forallprod ts v n sc f
  : lamn ts v n sc f
    ->
    forall x : HProdn.t v sc, f x.
  induction n.
  easy.
  intros.
  pose (IHn _ _ (X (fst x)) (snd x)).
  rewrite surjective_pairing.
  exact f0.
Qed.

Ltac prodSc x :=
  match x with
  | (_ ?ty * ?tl)%type => let tt := prodSc tl in constr:(Vector.cons _ ty _ tt)
  | Datatypes.unit     => constr:(Vector.nil {k & type k})
  end.

Ltac prodsize x :=
  match x with
  | (_ * ?t)%type  => let tt := prodsize t in constr:(S tt)
  | Datatypes.unit => constr:(0)
  end.

Ltac breakStore :=
  simpl str;
  let n := fresh "n" in
  let sc := fresh "sc" in
  (match goal with
   | |- forall _ : ?t, _ =>
     let n := prodsize t in
     let sc := prodSc t in
     apply (forallprod _
                       _ (*(qualified (typeConv wordOfSize))*)
                       n
                       sc
           )
   end;
   unfold lamn).

Ltac simplify := repeat match goal with
                        | |- forall _ : str, _ =>
                          breakStore;
                          lazy -[
                            BVplus BVminus BVmul BVquot
                            BVrotR BVrotL BVshiftL BVshiftR BVcomp
                            zero one
                            (*
                            fromNibbles
                              numBinOp numUnaryOp numBigargExop numOverflowBinop
                              Nat.add Nat.sub Nat.mul Nat.div Nat.pow
                              N.add N.sub N.mul N.div N.div_eucl N.modulo

                              Ox nth replace
                             *)
                          ];
                          repeat
                            (match goal with
                             | |- _ /\ _          => constructor
                             | |- _ -> _          => intro
                             | H : _ /\ _ |- _    => destruct H
                             | H : True |- _      => clear H
                             | |- True            => constructor
                             | |- ?x = ?x         => trivial
                             | H : True |- _           => clear H
                             | H : Datatypes.unit |- _ => clear H
                             end)
                        | |- forall _, _ => intro
                        | |- ?I          => unfold I
                        (* The next simply takes care of a functional
                           application. Should only be used once for
                           `tpt`
                        *)
                        | |- context f [ ?F _ ] => unfold F
                        end.
