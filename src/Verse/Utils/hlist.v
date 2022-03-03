(** * Hetrogeneous lists

A list that has elements of different sorts.

 *)

(* begin hide *)
Require Import List.
Require Import Program.Equality.

Import List.ListNotations.

Set Universe Polymorphism.
(* end hide *)

Section hlist.
  Context {sort : Type}(A : sort -> Type).

  Inductive hlist : list sort -> Type :=
  | hnil  : hlist []%list
  | hcons : forall x xs,  A x -> hlist xs -> hlist (x :: xs).

  (* member's arguments being ordered in this way allows existT's for instances
  to be written without filling out all holes *)
  Inductive member : list sort -> sort -> Type :=
  | hfirst : forall l elem, member (elem :: l) elem
  | hnext  : forall s0 l elem, member l elem -> member (s0 :: l) elem.

End hlist.
(* begin hide *)
Arguments hnil {sort A}.
Arguments hcons {sort A x xs}.
Arguments hfirst {sort l elem}.
Arguments hnext {sort s0 l elem}.
(* end hide *)

Declare Scope hlist_scope.

Infix "::" := (hcons) : hlist_scope.
Notation "[ ]" := (hnil) : hlist_scope.
Notation "[ X ]" := (hcons X hnil) : hlist_scope.
Notation "[ X ; Y ; .. ; Z ]" := (hcons X (hcons Y .. (hcons Z hnil) ..)) : hlist_scope.
Notation "X ∈ L" := (member L X)  (at level 70).
Infix "++" := app : hlist_scope.

Delimit Scope hlist_scope with hlist.
Bind Scope hlist_scope with hlist.


Definition hd {sort}{A : sort -> Type}{x: sort}{xs : list sort}
           (ha : hlist A (x :: xs)) : A x :=
  match ha with
  | hcons u _ => u
  end.

Definition tl {sort}{A : sort -> Type}{x: sort}{xs : list sort}
           (ha : hlist A (x :: xs)) : hlist A xs :=
  match ha with
  | hcons _ us => us
  end.

Definition hlist_eta {sort}{A : sort -> Type}{x : sort}{xs : list sort}
      (ha : hlist A (x :: xs)) : ha = (hd ha :: tl ha)%hlist
  := match ha with
     | hcons u us => eq_refl
     end.

Definition casenil [T] (A : T -> Type) (P:hlist A [] -> Type) (H:P []%hlist) hl:P hl :=
  (* TODO : Understand this devil business. Taken from VectorDef.case0 *)
  match hl with
  | []%hlist => H
  | _ => fun devil => False_ind (@IDProp) devil
  end.

Fixpoint map {sort}{A B : sort -> Type}{l : list sort}
         (f : forall s, A s -> B s) : hlist A l -> hlist B l :=
  match l with
  | []       => fun _ => hnil
  | (x :: xs) => fun us => hcons (f x (hd us)) (map f (tl us))
  end.

Fixpoint foldl {sort T}{A : sort -> Type}
         (func : forall s, T -> A s -> T) (t0 : T) {l}(hl : hlist A l): T
  := match hl with
     | []%hlist => t0
     | (x :: xs)%hlist => foldl func (func _ t0 x) xs
     end.


Fixpoint foldr {sort T}{A : sort -> Type}
         (func : forall s, A s -> T -> T)(t0 : T){l}(hl : hlist A l) : T
  := match hl with
    | []%hlist => t0
    | (x :: xs)%hlist => func _ x (foldr func t0 xs)
    end.

Definition toList {sort} {A : Type} {l : list sort} : hlist (fun _ : sort => A) l -> list A :=
  foldr (fun (_ : sort) (x : A) xs => (x :: xs)) [].

Fixpoint zipWith {sort}{A B C: sort -> Type}
         (func : forall s, A s -> B s -> C s) {l} : hlist A l -> hlist B l -> hlist C l :=
  match l with
  | [] => fun _ _ => []%hlist
  | _  => fun ha hb => (func _ (hd ha) (hd hb) :: zipWith func (tl ha) (tl hb))%hlist
  end.

Program Fixpoint app {sort}{A : sort -> Type}{l lp : list sort}
        (h : hlist A l) : hlist A lp -> hlist A (l ++ lp) :=
  match h in hlist _ l0
        return hlist A lp -> hlist A (l0 ++ lp) with
  | hnil =>  fun h => h
  | hcons x hs => fun h => hcons x (app hs h)
  end.

(* ** Hetrogeneous boolean equality on membership types *)
Section EqBool.
  Context {sort  : Type}.

  (* Hetrogeneous eqb *)
  Fixpoint heqb {s1 s2 : sort}{L1 L2 : list sort}(i1 : s1 ∈ L1)(i2 : s2 ∈ L2) : bool :=
    match i1, i2 with
    | hfirst, hfirst => true
    | hnext i1p, hnext i2p => heqb i1p i2p
    | _, _ => false
    end.

  Lemma heqb_sort {s1 s2 : sort}(L : list sort) :
    forall (i1 : s1 ∈ L)(i2 : s2 ∈ L), heqb i1 i2 = true -> s1 = s2.
    intros i1 i2.
    induction L; dependent destruction i1;
      dependent destruction i2; repeat (intuition; eauto).
  Qed.

  Lemma hneqb_type {s1 s2 : sort}(sNeq : s1 <> s2)(L : list sort) :
    forall (i1 : s1 ∈ L)(i2 : s2 ∈ L), heqb i1 i2 = false.
    intros i1 i2.
    induction L; dependent destruction i1;
      dependent destruction i2; simpl; intuition; eauto.
  Qed.

  Lemma eq_heqb s L (pf1 pf2 : s ∈ L) : pf1 = pf2 -> heqb pf1 pf2 = true.
    intro HeqPf. rewrite HeqPf.
    induction pf2; simpl; eauto.
  Qed.

  Lemma heqb_eq s L (pf1 pf2 : s ∈ L) : heqb pf1 pf2 = true -> pf1 = pf2.
    induction L;
    dependent destruction pf1;
    dependent destruction pf2; simpl; intuition;
    f_equal; eauto.
  Qed.

  Lemma heqb_eqSigT s1 s2 L (pf1 : s1 ∈ L) (pf2 : s2 ∈ L)
    : heqb pf1 pf2 = true -> existT (fun s => s ∈ L) s1 pf1 = existT _ s2 pf2.
    induction L;
      dependent destruction pf1; dependent destruction pf2;
      simpl; intuition.
    apply (f_equal (fun ss => existT _ _ (hnext (projT2 ss))) (IHL _ _ H)).
  Qed.

  Lemma hneqSigT_first (s1 s2 : sort) L (pf : s2 ∈ (s1::L))
    : existT (fun s => s ∈ (s1::L)) _ hfirst <> existT _ _ pf
      -> exists pf1, pf = hnext pf1.
  Proof.
    dependent destruction pf.
    + contradiction.
    + intro. now exists pf.
  Qed.

End EqBool.

Section ELift.

  Context {sort : Type}{T : Type}.
  Context (B : T -> sort -> Type).
  Fixpoint elift (ls : list sort) :=
    match ls as ls0
          return hlist (fun s => forall t : T, B t s) ls0 -> forall t : T, hlist (B t) ls0
    with
    | [] => fun _ => fun _ => hnil
    | (x :: xs) => fun hl => fun t => hcons (hd hl t) (elift xs (tl hl) t)
    end.

End ELift.

Arguments elift {sort T B} [ls].


Ltac induction_on hl :=
  let x   := fresh "x"   in
  let xs  := fresh "xs"  in
  let ax  := fresh "ax"  in
  let axs := fresh "axs" in
  let iH  := fresh "iH"  in
  induction hl as [ |x xs ax axs iH]; simpl; trivial;
  rewrite iH; simpl; trivial.

(** ** Indexing and updating hlists.

We using membership elements; they are the typed equivalent of In type
for list, indexing hetrogeneous lists element.

*)

Section Indexing.
  Context {sort : Type}{A : sort -> Type}.

  Fixpoint index {s}{ss : list sort}(idx : s ∈ ss)  :=
    match idx in s0 ∈ ss0 return hlist A ss0 -> A s0
    with
    |  hfirst     => hd
    |  hnext idx' => fun x => index idx' (tl x)
    end.

  Fixpoint update {s}{ss : list sort}(idx : s ∈ ss) :=
    match idx in s0 ∈ ss0 return hlist A ss0 -> A s0 -> hlist A ss0
    with
    | hfirst => fun x a => a :: tl x
    | hnext idx' => fun x a => hd x :: update idx' (tl x) a
    end%hlist.

  Fixpoint all_membership (l : list sort) : hlist (fun s => s ∈ l) l :=
    match l with
    | []%list => []%hlist
    | (x :: xs)%list => let xsslice := all_membership xs in
                      (hfirst :: hlist.map (fun tau (e : tau ∈ xs) => hnext e)  xsslice)
    end.

  Definition generate {l : list sort} (func : forall s, s ∈ l -> A s) : hlist A l :=
    map func (all_membership l).

  Lemma updated_index {s}{ss : list sort} (idx : s ∈ ss)
        (hl : hlist A ss) (x : A s)
    : index idx (update idx hl x) = x.
  Proof.
    induction idx.
    trivial.
    apply IHidx.
  Qed.

  Lemma update_other_index (s0 s1 : sort) (ss : list sort)
        (idx0 : s0 ∈ ss) (idx1 : s1 ∈ ss)
        (hl : hlist A ss) (x : A s0)
    : ~ existT _ _ idx1 = existT _ _ idx0
      -> index idx1 (update idx0 hl x) = index idx1 hl.
  Proof.
    (* TODO : Not sure this can be written without dependent induction *)
    intro.
    induction hl;
    dependent induction idx0;
      dependent induction idx1;
      try contradiction; trivial.
    apply IHhl.
    intro.
    pose (f_equal (fun sigs => existT (member (x0::xs)) _ (hnext (projT2 sigs))) (H0)).
    contradiction.
  Qed.

End Indexing.

(** Functional form of hlist *)
Definition functional {sort}{A : sort -> Type}{l : list sort} (hl : hlist A l)
  : forall s, s ∈ l -> A s :=
  fun _ mem => index mem hl.

Notation "L [@ i ]" := (index i L)  (at level 1, format "L [@ i ]").

Lemma index_map sort (A B  : sort -> Type) (func : forall s, A s -> B s)(l : list sort) s (pf : s ∈ l)  :
  forall hl : hlist A l, index pf (map func hl) = func s (index pf hl).
  intros.
  induction pf; simpl; trivial.
Qed.

Lemma all_membership_all sort (l : list sort) : forall s (pf : s ∈ l), index pf (all_membership l) = pf.
  intros.
  induction pf; simpl; trivial.
  rewrite index_map.
  now f_equal.
Qed.


(** ** Currying and Uncurring *)

Import EqNotations.
Section Currying.

  Context {sort : Type} (A : sort -> Type)(B : Type).

  Fixpoint curried (ss : list sort) : Type :=
    match ss with
    | []       => B
    | (x :: xs) => A x -> curried xs
    end.

  Lemma curried_cons ss s : curried (s :: ss) = (A s -> curried ss).
    trivial.
  Qed.

  Fixpoint curry ss : (hlist A ss -> B) -> curried ss :=
    match ss with
    | []       => fun func => func []%hlist
    | (x :: xs) => fun func =>  fun x => curry xs (fun (hls : hlist A xs) => func (x :: hls)%hlist)
    end.

  Fixpoint uncurry ss : curried ss -> hlist A ss -> B :=
    match ss as ss0 return curried ss0 -> hlist A ss0 -> B with
    | []       => fun b => fun _ => b
    | (x :: xs) => fun func => fun hls => uncurry xs (func (hd hls)) (tl hls)
    end.


  (** * Converting between equal types.

We often need to transport values over the equality given by
[curried_cons]. The helper function [bind] and [unbind] are what you
can use in this context. The names come their similarity with the bind
function in the monad setting.

   *)

  Definition bind {ss s}  (fn : A s -> curried ss) : curried (s :: ss) :=
    rew <- [fun T : Type => T] curried_cons ss s in fn.

  Definition unbind {ss s}  (fn : curried (s :: ss)) : A s -> curried ss :=
    rew [ fun T : Type => T] curried_cons ss s in fn.
End Currying.

Arguments curry {sort A B ss}.
Arguments uncurry {sort A B ss}.
Arguments bind {sort A B ss s}.
Arguments unbind {sort A B ss s}.

Fixpoint ForAll {sort:Type}{A : sort -> Type}{ss : list sort} : curried A Prop ss -> Prop
  := match ss as ss0 return curried A Prop ss0 -> Prop with
     | [] => fun x => x
     | (s0 :: ss0) => fun curP => forall x : A s0, ForAll (curP x)
     end.

Fixpoint Exists {sort}{A : sort -> Type}{ss : list sort} : curried A Prop ss -> Prop :=
  match ss as ss0 return curried A Prop ss0 -> Prop with
  | [] => fun x   => x
  | (s0 :: ss0) => fun curP => exists x : A s0, Exists (curP x)
  end.

(**  * Permuting hlists *)

Module Perm.

  Context [sort : Type]{L : list sort}.
  Record t := Perm { app  :> forall s : sort, s ∈ L -> s ∈ L ;
                     iapp : forall s : sort, s ∈ L -> s ∈ L ;
                     app_iapp_id : forall s (pf : s ∈ L), app s (iapp s pf) = pf;
                     iapp_app_id : forall s (pf : s ∈ L), iapp s (app s pf) = pf
                   }.

  Definition idPerm : t := Perm (fun _ pf => pf) (fun _ pf => pf) (fun _ _ => eq_refl) (fun _ _ => eq_refl).
  Definition inv (g : t) := Perm (iapp g) (app g) (iapp_app_id g) (app_iapp_id g).

  Notation "𝟙" := (idPerm).

  Definition permute {A : sort -> Type}(hl : hlist A L)(g : t) : hlist A L := generate (fun s mem => functional hl s (app g s mem)).

End Perm.
