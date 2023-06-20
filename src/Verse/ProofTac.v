(** Tactics for proof goal presentation *)
Require Import Verse.AnnotatedCode.
Require Import Verse.BitVector.
Require Import Verse.BitVector.ArithRing.
Require Import Verse.Machine.BitVector.
Require Import Verse.ModularCode.
Require Import Verse.Monoid.
Require Import Verse.Utils.hlist.
Require Import Verse.HlistMachine.

Require Import List.
Import List.ListNotations.

(* Destruct the variable store for easier access to valuations *)

Fixpoint hlamn [T] (A : T -> Type) (sc : list T)
  : (hlist A sc -> Type) -> Type
  := match sc as sc0
           return (hlist _ sc0 -> Type) -> Type
     with
     | []  => fun f => f []%hlist
     | n => fun f => forall a, hlamn _ _ (fun x => f (a::x)%hlist)
     end.

Definition forallhlist [T] (A : T -> Type) sc f
  : hlamn A sc f
    -> forall x : hlist A sc, f x.
  induction sc.
  now apply casenil.

  intros.
  pose (IHsc _ (X (hlist.hd x)) (hlist.tl x)).
  rewrite hlist_eta.
  exact f0.
Qed.

Ltac introHlamn :=
  repeat lazymatch goal with
         | |- hlamn _ nil _ => unfold hlamn
         | |- hlamn _ _ _   => intro
         end.

Ltac breakStore :=
  let rec break :=
    lazymatch goal with
    | |- forall _ : state _ _, _          => refine (forallhlist _ _ _ _);
                                             introHlamn
    | |- forall _ : Machine.memory _ _, _ => refine (forallhlist _ _ _ _);
                                             introHlamn
    | |- forall _, _                      => intro; break
    end in break.

Ltac unwrap := match goal with
               | |- ?I => try unfold I
               end; autounfold with Wrapper(*; simpl*).
               (* This `simpl` breaks field arithmetic proofs and also
               is a major slowdown for `realize`. If it turns out to
               be required, an easy fix is to write `modMod_add` for
               the `simpl`ed obligation that comes out. *)

(* The following directives make sure that `simpl` does not reduce bitvector operators when applied to a single concrete argument (say) which then interferes with presentation and/or applicability of lemmas.
For instance, shiftL in the subroutine demo for the thesis has a `BVshiftL 4 A` which gets simplified to BshiftL or so.

We might need to do this for all N, nat operators too in the long term *)
Arguments BVshiftL [sz] !_ !_.
Arguments BVshiftR [sz] !_ !_.
Arguments BVrotR [sz] !_ !_.
Arguments BVrotL [sz] !_ !_.
Arguments BVand [n] !_ !_.
Arguments BVor [n] !_ !_.
Arguments BVxor [n] !_ !_.

(* TODO : While the following two tactics are fairly generic, they
          don't work without specific BitVector functions. Needs to be
          organized better.
 *)

Ltac simplify := unfold getProp;
                 breakStore;
                 lazy -[ BVplus BVminus BVmul BVquot
                         And Or Xor Not BVrotR BVrotL BVshiftL BVshiftR BVcomp
                         zero one

                         (*Nat.add Nat.sub Nat.mul Nat.div Nat.pow*)
                         (* Parametric arithmetic of shift parameters
                         is sha need the above to not be
                         unfolded. However, power computations, N2Bv
                         implicit parameter computations and len/pos
                         computations in curve25519 field arithmetic
                         need these to be computed. The fix that works
                         'for now' is folding these post the
                         expansion. *)
                   ] in *; fold Nat.add Nat.sub Nat.mul Nat.div Nat.pow in *;

                 repeat
                   (match goal with
                    | |- _ -> _          => intro
                    | |- forall _, _     => intro
                    | H : _ /\ _ |- _    => destruct H
                    | H : True |- _      => clear H
                    | H : Datatypes.unit |- _ => clear H
                    end);
                 repeat
                   (match goal with
                    | |- True            => constructor
                    | |- ?x = ?x         => trivial
                    | |- _ /\ _          => constructor
                    | _                  => try trivial
                    end).
                   (*                 | |- forall _, _ => intro*)
(* The next should only ever be invoked
                           for a Prop generated by `tpt` *)
(*                 | |- ?I          => unfold I;
                                     autounfold with Wrapper *)(*unfold I;
                                            unfold tpt;
                                            unfold cp*)
                   (*                        | |- getProp _ _ => first [ modProof | unfold getProp ]*)
(* The next simply takes care of a functional
                           application. Should only be used once for
                           `tpt`
 *)
(*| |- context f [ ?F _ ] => unfold F*)

Ltac realize := unwrap; simplify.

Ltac modProof :=
  try match goal with
      | |- context [getProp _ (linesDenote (inline_calls ?l))]
        => rewrite (splitEq l); apply modularize;
           unfold modularProof; simpl;
           repeat match goal with
                  | |- distinctAll _ /\ _ =>  constructor;
                                              [> unfold distinctAll; simpl; easy
                                              | breakStore ]
                  end
      end.


Ltac mrealize := unwrap; modProof;
                 try simplify.

Require Import Verse.Scope.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.

Fixpoint swapScope [t] [v : Variables.U t]
         (vT : Scope.type t) [typ C]
  : (scoped v vT (typ -> C)) -> (typ -> scoped v vT C) :=
  match vT with
  | []         => id
  | (_ :: vTt) => fun s x vty => swapScope _ (s vty) x
  end.


Definition swapGScope [t] (vT : Scope.type t)
           [typ] [C : Variables.U t -> Type]
  : (forall v, scoped v vT (typ -> C v)) -> typ -> forall v, scoped v vT (C v)
    := fun f => fun t v => (swapScope vT (f v) t).

Ltac mapTyOf xt :=
  match xt with
  | Cookup.var ?y -> ?z => refine (y :: _)%list; mapTyOf z
  | ?x                     => exact ([]%list)
  end.

(* Extract the scope out of a generic function *)
Ltac getScope x := let xt := type of (x Cookup.var) in mapTyOf xt.

Ltac rearrScope x :=
  let scp := fresh "scp" in
  let sc  := fresh "sc"  in
  let typ := fresh "typ" in
  let rx  := fresh "rx"  in
  (* Bring out the leading scope and the scoped Type *)
  simple refine (let scp : Scope.type verse_type_system := _ in _);
  [getScope x | idtac];
  simpl in *;
  let nx := fresh "nx" in
  tryif
    (* Swap out one inner parameter if possible *)
    pose (nx := swapGScope scp x)
  then
    (* Recursively call rearrScope to check for more inner parameters *)
    let t := fresh "t" in
    match type of nx with
    | ?T -> _ => refine (fun t : T => _)
    end;
    let nxn := fresh "nxn" in
    pose (nxn := nx t);
    simpl in nxn;
    rearrScope nxn
  else
    exact x.

(* Parametrize target Prop on non-variable parameters *)
Ltac parametrize x :=
  lazymatch type of x with
  | Variables.U verse_type_system -> _ => AnnotatedCode.getProp x
  | ?T -> _                            => let t := fresh "t" in
                                          refine (forall t : T, _ : Prop);
                                          parametrize (x t)
  end.

(* Final tactic to extract a Prop from an annotated code block
     with mixed scope *)
Ltac exParamProp x :=
  let tmp := fresh "tmp" in
  simple refine (let tmp : _ := _ in _);
  [shelve | rearrScope x | idtac];
  simpl in tmp; idtac tmp; parametrize tmp.
