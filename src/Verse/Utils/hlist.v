(** * Hetrogeneous lists

A list that has elements of different sorts.

 *)

(* begin hide *)
Require Import List.
Import List.ListNotations.
(* end hide *)

Section hlist.
  Context {sort : Type}(A : sort -> Type).

  Inductive hlist : list sort -> Type :=
  | hnil  : hlist []%list
  | hcons : forall x xs,  A x -> hlist xs -> hlist (x :: xs).

  Context (elem : sort).

  Inductive member : list sort -> Type :=
  | hfirst : forall l, member (elem :: l)
  | hnext  : forall s0 l, member l -> member (s0 :: l).

End hlist.
(* begin hide *)
Arguments hnil {sort A}.
Arguments hcons {sort A x xs}.
Arguments hfirst {sort elem l}.
Arguments hnext {sort elem s0 l}.
(* end hide *)

Declare Scope hlist_scope.

Infix "::" := (hcons) : hlist_scope.
Notation "[ ]" := (hnil) : hlist_scope.
Notation "[ X ]" := (hcons X hnil) : hlist_scope.
Notation "[ X ; Y ; .. ; Z ]" := (hcons X (hcons Y .. (hcons Z hnil) ..)) : hlist_scope.
Notation "X ∈ L" := (member X L)  (at level 70).
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
  Context {sort : Type}{A : sort -> Type} {s : sort} .

  Fixpoint index {ss : list sort}(idx : s ∈ ss)  :=
    match idx in _ ∈ ss0 return hlist A ss0 -> A s
    with
    |  hfirst => hd
    |  hnext idx' => fun x => index idx' (tl x)
    end.

  Fixpoint update {ss : list sort}(idx : s ∈ ss) :=
    match idx in _ ∈ ss0 return hlist A ss0 -> A s -> hlist A ss0
    with
    | hfirst => fun x a => a :: tl x
    | hnext idx' => fun x a => hd x :: update idx' (tl x) a
    end%hlist.

End Indexing.

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
