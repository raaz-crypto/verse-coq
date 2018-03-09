Require Import Verse.Error.
Require Import Verse.Word.

Require Import Arith.
Require Import Nat.
Require Import Max.
Require Import Min.
Require Import Omega.

Inductive BoundError : Prop := Overflow | Underflow | DivByZero.

Section BoundedOperations.

  Variable n : nat.

  Local Definition size := 8 * 2^n.

  Definition bounds := { p : nat * nat | fst p <= snd p <= size }.

  Variable b1 b2 b3 : bounds.

  (* Checks if upper bound exceeds size *)
  Local Definition ofc (p : { pp : nat * nat | fst pp <= snd pp }) : bounds + {BoundError} :=
    let 'exist _ (l, u) pl := p in
    match le_dec u size with
    | left pu => {- exist _ (l, u) (conj pl pu) -}
    | _       => error Overflow
    end.

  (* Lifts component errors out from a pair *)
  Local Definition pErr {Err : Prop} {T} (p : (T + {Err}) * (T + {Err}))
    := let '(l,u) := p in
       match l, u with
       | {- lv -}, {- uv -}  => {- (lv, uv) -}
       | error e , _         => error e
       | _       , error e   => error e
       end.

  Local Definition Max a b := if Nat.eq_dec a b then a + 1 else max a b.

  Local Notation exP A := (exist _ A _).
  Local Notation l_b b   := (fst (proj1_sig b)).
  Local Notation u_b b   := (snd (proj1_sig b)).

  Hint Unfold Max.

  Ltac boundCheck := repeat (simpl in *; autounfold in *;
                             match goal with
                             | H : bounds |- context [?H]  => let x := fresh "x" in destruct H as [x];
                                                                                    destruct x; clear H
                             | |- context [if ?H then _ else _] => destruct H
                             | |- context [Nat.max ?A ?B] => let mx := fresh "mx" in
                                                             pose (mx := Nat.max A B);
                                                             let mxl := fresh "mxl" in
                                                             let mxr := fresh "mxr" in
                                                             pose (mxl := le_max_l A B); pose (mxr := le_max_r A B);
                                                             change (Nat.max A B) with mx; change (Nat.max A B) with mx in mxl, mxr
                             | |- context [Nat.min ?A ?B] => let mn := fresh "mn" in
                                                             pose (mn := Nat.min A B);
                                                             let mnl := fresh "mnl" in
                                                             let mnr := fresh "mnr" in
                                                             pose (mnl := le_min_l A B); pose (mnr := le_min_r A B);
                                                             change (Nat.min A B) with mn; change (Nat.min A B) with mn in mnl, mnr
                             | H := Nat.min ?A ?B : _ |- _ => let x := fresh "x" in
                                                              (destruct (min_dec A B) as [x|x];
                                                               change (Nat.min A B) with H in x;
                                                               omega)
                             | H := Nat.max ?A ?B : _ |- _ => let x := fresh "x" in
                                                              (destruct (max_dec A B) as [x|x];
                                                               change (Nat.max A B) with H in x;
                                                               omega)
                             | _ => idtac
                             end); try omega.

  Definition add : bounds + {BoundError}.
    refine (ofc (exP (Max (l_b b1) (l_b b2), max (u_b b1) (u_b b2) + 1))).
    boundCheck.
  Defined.

  Definition subtract : bounds + {BoundError}.
    refine (if lt_dec (u_b b2) (l_b b1) then
              ofc (exP (if zerop (u_b b2)
                        then (l_b b1)
                        else (l_b b1) - 1, u_b b1))
            else
              error Underflow).
    boundCheck.
  Defined.

  Definition multiply : bounds + {BoundError}.
    refine (ofc (exP ((l_b b1) + (l_b b2), (u_b b1) + (u_b b2)))).
    boundCheck.
  Defined.

  Definition exmultiply : (bounds + {BoundError}) * (bounds + {BoundError}).
    refine (mapP ofc (if le_lt_dec (u_b b1 + u_b b2) size
                      then
                        (exP (0, 0), exP ((l_b b1) + (l_b b2), (u_b b1) + (u_b b2)))
                      else
                        (if le_lt_dec (l_b b1 + l_b b2) size
                         then
                           exP (0, u_b b1 + u_b b2 - size)
                         else
                           exP (l_b b1 + l_b b2 - size, u_b b1 + u_b b2 - size),
                         exP (0, size)))
           );
      boundCheck.
  Defined.

  Definition divide : bounds + {BoundError}.
    refine (if zerop (l_b b2)
            then error DivByZero
            else
              ofc (exP ((l_b b1) - (u_b b2), (u_b b1) - (l_b b2) + 1))).
    boundCheck.
  Defined.

  Definition quotrem : (bounds + {BoundError}) * (bounds + {BoundError}).
    refine (if zerop (l_b b3)
            then (error DivByZero, error DivByZero)
            else (if zerop (u_b b1)
                 then
                   ofc (exP ((l_b b2) - (u_b b3), (u_b b2) - (l_b b3) + 1))
                 else if zerop (l_b b1)
                      then
                        ofc (exP ((l_b b2) - (u_b b3), (u_b b1) + size - (l_b b3) + 1))
                      else
                        ofc (exP ((l_b b1) + size - (u_b b3), (u_b b1) + size - (l_b b3) + 1)),
                  ofc (exP (0, (u_b b3)))));
      boundCheck.
  Defined.

  Definition remainder : bounds + {BoundError}.
    refine (if zerop (l_b b2)
            then error DivByZero
            else if zerop (l_b b1)
                 then if zerop (u_b b1)
                      then ofc (exP (0,0))
                      else ofc (exP (0, (u_b b2)))
                 else ofc (exP (0, (u_b b2))));
    boundCheck.
  Defined.

  Definition bitOr : bounds + {BoundError}.
    refine (ofc (exP (if lt_dec (u_b b2) (l_b b1)
                      then (l_b b1)
                      else if lt_dec (u_b b1) (l_b b2)
                           then (l_b b2)
                           else 0,
                      max (u_b b1) (u_b b2)))).
    boundCheck.
  Defined.

  Definition bitAnd : bounds + {BoundError}.
    refine (ofc (exP (match Nat.eq_dec (l_b b1) (u_b b1), Nat.eq_dec (l_b b2) (u_b b2), Nat.eq_dec (u_b b1) (l_b b2) with
                      | left _, left _, left _ => (l_b b1)
                      | _, _, _ => 0
                      end, min (u_b b1) (u_b b2)))).
    boundCheck.
  Defined.

  Definition bitXor : bounds + {BoundError}.
    refine (ofc (exP (if lt_dec (u_b b2) (l_b b1)
                      then (l_b b1)
                      else if lt_dec (u_b b1) (l_b b2)
                           then (l_b b2)
                           else 0,
                      match Nat.eq_dec (l_b b1) (u_b b1), Nat.eq_dec (l_b b2) (u_b b2), Nat.eq_dec (u_b b1) (l_b b2) with
                      | left _, left _, left _ => (u_b b1) - 1
                      | _, _, _ => max (u_b b1) (u_b b2)
                      end))).
    boundCheck.
  Defined.

  Definition bitComp : bounds + {BoundError}.
    refine (ofc (exP (if lt_dec (u_b b1) size
                      then (size, size)
                      else (0, size - 1)))).
    boundCheck.
  Defined.

  Local Lemma modBound m : m mod size < size.
  Proof.
    refine (Nat.mod_upper_bound m size _).
    unfold size.
    assert (eight : 8 = 2 ^ 3); trivial.
    rewrite eight.
    rewrite <- Nat.pow_add_r.
    apply Nat.pow_nonzero.
    inversion 1.
  Qed.

  Definition rotL (m : nat) : bounds + {BoundError}.
    refine (let mm := m mod size in
            if le_dec (size - mm + 1) (l_b b1)
            then
              ofc (exP ((l_b b1) - size + mm, size))
            else if le_dec (size - mm + 1) (u_b b1)
                 then ofc (exP (if zerop (l_b b1)
                                then 0
                                else 1,
                                size))
                 else
                   ofc (exP ((l_b b1) + mm, (u_b b1) + mm))).
    change mm with (m mod size) in *.
    pose (modBound m).
    all: boundCheck.
  Defined.

  Definition rotR (m : nat) : bounds + {BoundError}.
    refine (let mm := m mod size in
            ofc (exP (if zerop (l_b b1)
                      then 0
                      else if le_dec (u_b b1) mm
                           then size + (l_b b1) - mm
                           else if le_dec (l_b b1) mm
                                then 1
                                else l_b b1 - mm,
                      if le_dec (u_b b1) mm
                      then size + (u_b b1) - mm
                      else size))).
    change mm with (m mod size) in *.
    pose (mB := modBound m).
    all: boundCheck.
  Defined.

  Definition shiftL (m : nat) : bounds + {BoundError}.
    refine (if lt_dec (size - m) (u_b b1)
            then error Overflow
            else ofc (exP ((l_b b1) + m, (u_b b1) + m))).
    boundCheck.
  Defined.

  Definition shiftR (m : nat) : bounds + {BoundError}.
    refine (ofc (exP (max ((l_b b1) - m) 0, max ((u_b b1) - m) 0))).
    boundCheck.
  Defined.

End BoundedOperations.