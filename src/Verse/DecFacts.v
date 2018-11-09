Require Import Verse.Word.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Language.
Require Import Verse.Syntax.

Require Import PeanoNat.
Require Import Eqdep_dec.
Require Import Bool.
Require Import Equality.
Require Import Vector.
Import VectorNotations.
Require Import VectorEq.

Set Implicit Arguments.
Generalizable All Variables.


Notation decidable P := ({P} + {~ P}) (only parsing).

Theorem dec_not_not : forall P:Prop, decidable P -> (~ P -> False) -> P.
Proof.
tauto.
Defined.

Theorem dec_True : decidable True.
Proof.
auto.
Defined.

Theorem dec_False : decidable False.
Proof.
unfold not; auto.
Defined.

Theorem dec_or :
 forall A B:Prop, decidable A -> decidable B -> decidable (A \/ B).
Proof.
tauto.
Defined.

Theorem dec_and :
 forall A B:Prop, decidable A -> decidable B -> decidable (A /\ B).
Proof.
tauto.
Defined.

Theorem dec_not : forall A:Prop, decidable A -> decidable (~ A).
Proof.
tauto.
Defined.

Theorem dec_imp :
 forall A B:Prop, decidable A -> decidable B -> decidable (A -> B).
Proof.
tauto.
Defined.

Theorem dec_iff :
 forall A B:Prop, decidable A -> decidable B -> decidable (A<->B).
Proof.
tauto.
Defined.

Theorem iff_dec :
  forall A B:Prop, A <-> B -> decidable A -> decidable B.
Proof.
  intros A B H AOR.
  destruct AOR as [a | na].
  left; apply H; easy.
  right; intro; contradict na; apply H; easy.
Defined.

Notation eq_dec A := (forall A1 A2 : A, {A1 = A2} + {A1 <> A2}) (only parsing).

Definition nat_eq_dec : eq_dec nat := Nat.eq_dec.
Definition bool_eq_dec : eq_dec bool := bool_dec.

Hint Resolve dec_True dec_False dec_or dec_and dec_imp dec_not dec_iff nat_eq_dec bool_eq_dec
 : decidable_prop.

Ltac solve_decidable :=
  match goal with
  | |- decidable _ => solve [ auto 100 with decidable_prop core ]
  end.

Lemma eq_dec_refl {T} (T_eq_dec : eq_dec T) (t : T)
  : {p : t = t | T_eq_dec t t = left p}.
  pose (T_eq_dec t t).
  change (T_eq_dec t t) with s.
  destruct s.
  destruct e. exists eq_refl; trivial.
  destruct n; trivial.
Qed.

Lemma eq_dec_neq {T} (T_eq_dec : eq_dec T) (t1 t2 : T)
  : t1 <> t2 -> { p : t1 <> t2 | T_eq_dec t1 t2 = right p}.
  intros.
  pose (T_eq_dec t1 t2).
  change (T_eq_dec t1 t2) with s.
  destruct s;
    [contradiction | ].
  exists n; trivial.
Qed.

(* undep_eq not actually used any more *)
(*
Ltac undep_eq :=
  match goal with
  | [ H : existT _ _ ?a = existT _ _ ?b |- _ ]
    => let He := fresh H in
       assert (He : a = b) by (refine (inj_pair2_eq_dec _ _ _ _ _ _ H);
                             auto with decidable_prop);
       rewrite He in *; clear H
  end.
*)
Ltac crush_eq_dec := repeat aux_match; aux_solve
  with aux_match :=  (intros;
                     match goal with
                     | [ H1 : ?T, H2 : ?T, _ : _ <> _ |- _ ] => idtac
                     | [ H1 : ?T, H2 : ?T, H3 : ?T |- _ ]    => aux_cases2 H1 H3 T
                     | [ H1 : ?T, H2 : ?T |- _ ]             => aux_cases H1 H2 T
                     end)
  with aux_cases H1 H2 T :=
                       let T_eq_dec := fresh "T" in assert (T_eq_dec : eq_dec T) by (intros; solve_decidable);
                                                    destruct (T_eq_dec H1 H2) as [ eq | ];
                                                    [ subst | ..]; clear T_eq_dec
  (* Heuristic for pairing up four hypothesis of the same type by alternation *)
  with aux_cases2 H1 H2 T :=
                       let T_eq_dec := fresh "T" in assert (T_eq_dec : eq_dec T) by (intros; solve_decidable);
                                                    destruct (T_eq_dec H1 H2) as [ eq | ];
                                                    [ symmetry in eq; subst | ..]; clear T_eq_dec
  with aux_solve := try solve [left; constructor; trivial |
                               right; inversion 1; try congruence; easy ].

Ltac crush_eqb_eq :=
  repeat (match goal with
          | [ |- _ <-> _ ] => constructor
          | |- context [?H ?x ?x] => destruct (eq_dec_refl H x) as [eq deceq]; rewrite deceq; trivial
          | H : ?a = ?a -> False |- _ => contradict H; trivial
          | H : ?a = ?b -> False |- context [?Heq_dec ?a ?b] => destruct (Heq_dec a b)
          | |- _ -> _ => intros
          | H : _ = _ |- _ => dependent destruction H
          | _ => try contradiction
          end; autounfold in *).

Section DecFacts.

  Variable T : Type.
  Variable T_dec : forall (a b : T), decidable (a = b).

  (* Boolean equality for decidable Types *)
  Definition eqdec_eqb := fun a b => if T_dec a b then true else false.

  Definition eqdec_eqb_eq : forall a b, eqdec_eqb a b = true <-> a = b.
    unfold eqdec_eqb. intros.
    destruct (T_dec a b);
      unfold iff; split; first [discriminate | contradiction | trivial].
  Defined.

  (* Vector equality is decidable *)
  Definition vec_eq_dec n : eq_dec (Vector.t T n).
    apply (Vector.eq_dec T eqdec_eqb eqdec_eqb_eq).
  Defined.

End DecFacts.

(** Decidable equality for Verse constructs *)

Lemma kind_eq_dec : eq_dec kind.
  refine (
  fun k1 k2 => match k1, k2 with
               | direct, direct => left eq_refl
               | memory, memory => left eq_refl
               | _, _           => right _
               end); intro; exact (match H with end).
Defined.

Lemma endian_eq_dec : eq_dec endian.
  refine (fun e1 e2 => match e1, e2 with
                       | hostE, hostE
                       | bigE, bigE
                       | littleE, littleE => left eq_refl
                       | _, _ => right _
                       end); inversion 1.
Defined.

Hint Resolve vec_eq_dec kind_eq_dec endian_eq_dec : decidable_prop.

Lemma directTy_eq_dec : eq_dec (type direct).
  refine (fun ty => match ty as ty0 in type direct return
                          forall ty' : type direct, {ty0 = ty'} + {ty0 <> ty'} with
                    | word n => fun ty' => match ty' as ty0' in type direct
                                                 return
                                                 {word n = ty0'} + {word n <> ty0'}
                                           with
                                           | word n' => _
                                           | multiword _ _ => _
                                           end
                    | multiword m n => fun ty' => match ty' as ty0' in type direct
                                                        return
                                                        {multiword m n = ty0'} + {multiword m n <> ty0'}
                                                  with
                                                  | word _ => _
                                                  | multiword m' n' => _
                                                  end
                    end).
  all: crush_eq_dec.
(*
  refine (fun (ty ty' : type direct) => match ty in type direct, ty' as ty0' in type direct return {ty = ty0'} + {ty <> ty'} with
                        | word n, word n' => if nat_eq_dec n n'
                                             then _
                                             else _
                        | multiword n m, multiword n' m' => if nat_eq_dec n n'
                                                            then if nat_eq_dec m m'
                                                                 then left _
                                                                 else right _
                                                            else right _
                        | _, _ => right _
                        end).
 *)
(*
  dependent destruction A1; dependent destruction A2; crush_eq_dec.
 *)
Defined.

Hint Resolve directTy_eq_dec.

Lemma ty_eq_dec : forall {k}, eq_dec (type k).
  induction k.
  apply directTy_eq_dec.
  intros ty ty'.
  refine (match ty, ty' with
          | array n e t, array n' e' t' => _
          end).
  crush_eq_dec.
Defined.

Lemma bytes_eq_dec : forall (n : nat), eq_dec (bytes n).
  destruct A1. destruct A2.
  unfold Bvector.Bvector in b, b0.
  crush_eq_dec.
Defined.

Hint Resolve ty_eq_dec bytes_eq_dec : decidable_prop.

Lemma op_eq_dec {la ra} : eq_dec (op la ra).
  refine (
  fun o1 o2 => match o1 as o1' in op la' ra'
                     return forall o : op la' ra', {o1' = o} + {o1' <> o}
               with
               | plus    => fun o => match o as o' in op unary binary
                                           return {plus = o'} + {plus <> o'}
                                     with
                                     | plus => _
                                     | _    => _
                                     end
               | minus   => fun o => match o as o' in op unary binary
                                           return {minus = o'} + {minus <> o'}
                                     with
                                     | minus => _
                                     | _     => _
                                     end
               | mul     => fun o => match o as o' in op unary binary
                                           return {mul = o'} + {mul <> o'}
                                     with
                                     | mul   => _
                                     | _     => _
                                     end
               | quot     => fun o => match o as o' in op unary binary
                                           return {quot = o'} + {quot <> o'}
                                     with
                                     | quot  => _
                                     | _    => _
                                      end
               | rem      => fun o => match o as o' in op unary binary
                                            return {rem = o'} + {rem <> o'}
                                      with
                                      | rem  => _
                                      | _    => _
                                      end
               | bitOr    => fun o => match o as o' in op unary binary
                                            return {bitOr = o'} + {bitOr <> o'}
                                      with
                                      | bitOr  => _
                                      | _    => _
                                      end
               | bitAnd   => fun o => match o as o' in op unary binary
                                            return {bitAnd = o'} + {bitAnd <> o'}
                                      with
                                      | bitAnd  => _
                                      | _    => _
                                      end
               | bitXor   => fun o => match o as o' in op unary binary
                                            return {bitXor = o'} + {bitXor <> o'}
                                      with
                                      | bitXor  => _
                                      | _    => _
                                      end
               | bitComp  => fun o => match o as o' in op unary unary
                                            return {bitComp = o'} + {bitComp <> o'}
                                      with
                                      | bitComp => _
                                      | _       => _
                                      end
               | rotL n   => fun o => match o as o' in op unary unary
                                            return {rotL n = o'} + {rotL n <> o'}
                                      with
                                      | rotL n' => _
                                      | _       => _
                                      end
               | rotR n   => fun o => match o as o' in op unary unary
                                            return {rotR n = o'} + {rotR n <> o'}
                                      with
                                      | rotR n' => _
                                      | _       => _
                                      end
               | shiftL n   => fun o => match o as o' in op unary unary
                                            return {shiftL n = o'} + {shiftL n <> o'}
                                      with
                                      | shiftL n' => _
                                      | _       => _
                                      end
               | shiftR n   => fun o => match o as o' in op unary unary
                                            return {shiftR n = o'} + {shiftR n <> o'}
                                      with
                                      | shiftR n' => _
                                      | _         => _
                                        end
               | nop        => fun o => match o as o' in op unary unary
                                              return {nop = o'} + {nop <> o'}
                                        with
                                        | nop  => _
                                        | _    => _
                                        end
               | exmul      => fun o => match o as o' in op binary binary
                                              return {exmul = o'} + {exmul <> o'}
                                        with
                                        | exmul => _
                                        | _ => _
                                        end
               | eucl       => fun o => match o as o' in op binary ternary
                                              return {eucl = o'} + {eucl <> o'}
                                        with
                                        | eucl  => _
                                        | _     => _
                                        end
               end o2); solve [exact idProp | crush_eq_dec].
Defined.

Hint Resolve vec_eq_dec kind_eq_dec endian_eq_dec ty_eq_dec bytes_eq_dec op_eq_dec
  : decidable_prop.

(* Equality is decidable for scopeVar *)

Fixpoint idxInScope n (vT : Vector.t (some type) n)
         k (ty : type k) (x : scopeVar vT ty) : nat  :=
  match x with
  | headVar    => 0
  | restVar x' => S (idxInScope x')
  end.

Definition scopeVar_eqb n (vT : Vector.t (some type) n)
           k (ty : type k) (x y : scopeVar vT ty) : bool :=
  if Nat.eq_dec (idxInScope x) (idxInScope y)
  then true else false.

Definition scopeVar_eqb_eq n (vT : Vector.t (some type) n)
           k (ty : type k) (x y : scopeVar vT ty) : scopeVar_eqb x y = true <-> x = y.
  constructor.
  * intro eqb_x_y.
    unfold scopeVar_eqb in eqb_x_y.
    simpl in eqb_x_y.
    destruct (Nat.eq_dec (idxInScope x) (idxInScope y));
      [idtac | discriminate].

    dependent induction x; dependent induction y.
  - trivial.
  - contradict e; discriminate.
  - contradict e; discriminate.
  - f_equal.
    apply IHx. apply (eq_add_S _ _ e).
    all: trivial.
  * intro.
    unfold scopeVar_eqb.
    rewrite H.
    destruct (Nat.eq_dec (idxInScope y) (idxInScope y));
      congruence.
Qed.

Definition scopeVar_eq_dec n (vT : Vector.t (some type) n)
  : forall {k} {ty : type k}, eq_dec (scopeVar vT ty).
  dependent induction A1; dependent induction A2;
    [left | right .. | idtac]; try congruence.
  destruct (IHA1 A2);
    [left; congruence | right].
  contradict n;
  apply (f_equal ((fun (y : scopeVar (tl v) ty) (x : scopeVar v ty) =>
                    (match x in @scopeVar (S n0) v0 _ ty0
                          return scopeVar (tl v0) ty0 -> scopeVar (tl v0) ty0 with
                    | headVar => fun y => y
                    | restVar x' => fun _ => x'
                    end y)) A1)
                 n).
Defined.
