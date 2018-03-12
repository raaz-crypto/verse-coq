Require Import Verse.Error.
Require Import Verse.Word.

Require Import Arith.

Require Import Max.
Require Import Min.
Require Import Omega.


Inductive BoundError : Prop :=
| InCorrectBounds : nat -> nat -> BoundError
| Overflow | Underflow | DivByZero.

Section BoundedOperations.

  Variable n : nat.

  Local Definition size := 8 * 2^n.

  Definition bounds : Type := nat * nat.

  Variable b1 b2 b3 : bounds.

  (* Checks if upper bound exceeds size *)
  Local Definition ofc (p : bounds) : bounds + {BoundError} :=
    let '(l, u) := p in
    match le_dec l u, le_dec u size with
    | left _, left _   => {- (l, u) -}
    | right _, _     => error (InCorrectBounds l u)
    | _, right _     => error Overflow
    end.

  (* Lifts component errors out from a pair *)
  Local Definition pErr {Err : Prop} {T} (p : (T + {Err}) * (T + {Err}))
    := let '(l,u) := p in
       match l, u with
       | {- lv -}, {- uv -}  => {- (lv, uv) -}
       | error e , _         => error e
       | _       , error e   => error e
       end.



  Local Notation l_b   := fst.
  Local Notation u_b   := snd.

  Definition add : bounds + {BoundError} :=
    ofc (if Nat.eq_dec (l_b b1) (l_b b2)
         then if zerop (l_b b1)
              then 0
              else l_b b1 + 1
         else max (l_b b1) (l_b b2),
         if zerop (u_b b1)
         then (u_b b2)
         else if zerop (u_b b2)
              then (u_b b1)
              else max (u_b b1) (u_b b2) + 1).


  Definition subtract : bounds + {BoundError} :=
    if lt_dec (u_b b2) (l_b b1) then
      ofc (if zerop (u_b b2)
           then (l_b b1)
           else (l_b b1) - 1, u_b b1)
    else
      if zerop (u_b b2)
      then ofc (0, u_b b1)
      else error Underflow.


  Definition multiply : bounds + {BoundError} :=
    ofc ((l_b b1) + (l_b b2), (u_b b1) + (u_b b2)).

  Definition exmultiply : (bounds + {BoundError}) * (bounds + {BoundError}) :=
    mapP ofc (if le_lt_dec (u_b b1 + u_b b2) size
              then
                ((0, 0), ((l_b b1) + (l_b b2), (u_b b1) + (u_b b2)))
              else
                (if le_lt_dec (l_b b1 + l_b b2) size
                 then
                   (0, u_b b1 + u_b b2 - size)
                 else
                   (l_b b1 + l_b b2 - size, u_b b1 + u_b b2 - size),
                 (0, size))).

   Definition divide : bounds + {BoundError} :=
     if zerop (l_b b2)
     then error DivByZero
     else
       ofc ((l_b b1) - (u_b b2), (u_b b1) - (l_b b2) + 1).

  Definition quotrem : (bounds + {BoundError}) * (bounds + {BoundError}) :=
    if zerop (l_b b3)
    then (error DivByZero, error DivByZero)
    else mapP ofc (if zerop (u_b b1)
                   then
                     ((l_b b2) - (u_b b3), (u_b b2) - (l_b b3) + 1)
                   else if zerop (l_b b1)
                        then
                          ((l_b b2) - (u_b b3), (u_b b1) + size - (l_b b3) + 1)
                        else
                          ((l_b b1) + size - (u_b b3), (u_b b1) + size - (l_b b3) + 1),
                   (0, (u_b b3))).

  Definition remainder : bounds + {BoundError} :=
    if zerop (l_b b2)
    then error DivByZero
    else ofc (if zerop (l_b b1)
              then if zerop (u_b b1)
                   then (0,0)
                   else (0, (u_b b2))
              else (0, (u_b b2))).

  Definition bitOr : bounds + {BoundError} :=
    ofc (if lt_dec (u_b b2) (l_b b1)
                      then (l_b b1)
                      else if lt_dec (u_b b1) (l_b b2)
                           then (l_b b2)
                           else 0,
                      max (u_b b1) (u_b b2)).

  Definition bitAnd : bounds + {BoundError} :=
    ofc (match Nat.eq_dec (l_b b1) (u_b b1), Nat.eq_dec (l_b b2) (u_b b2), Nat.eq_dec (u_b b1) (l_b b2) with
         | left _, left _, left _ => (l_b b1)
         | _, _, _ => 0
         end, min (u_b b1) (u_b b2)).

  Definition bitXor : bounds + {BoundError} :=
    ofc (if lt_dec (u_b b2) (l_b b1)
                      then (l_b b1)
                      else if lt_dec (u_b b1) (l_b b2)
                           then (l_b b2)
                           else 0,
         match Nat.eq_dec (l_b b1) (u_b b1), Nat.eq_dec (l_b b2) (u_b b2), Nat.eq_dec (u_b b1) (l_b b2) with
         | left _, left _, left _ => (u_b b1) - 1
         | _, _, _ => max (u_b b1) (u_b b2)
         end).

  Definition bitComp : bounds + {BoundError} :=
    ofc (if lt_dec (u_b b1) size
         then (size, size)
         else (0, size - 1)).


  Definition rotL (m : nat) : bounds + {BoundError} :=
    let mm := m mod size in
    ofc (if le_dec (size - mm + 1) (l_b b1)
         then
           ((l_b b1) - size + mm, size)
         else if le_dec (size - mm + 1) (u_b b1)
              then (if zerop (l_b b1)
                    then 0
                    else 1,
                    size)
              else
                ((l_b b1) + mm, (u_b b1) + mm)).

  Definition rotR (m : nat) : bounds + {BoundError} :=
    let mm := m mod size in
    ofc (if zerop (l_b b1)
         then 0
         else if le_dec (u_b b1) mm
              then size + (l_b b1) - mm
              else if le_dec (l_b b1) mm
                   then 1
                   else l_b b1 - mm,
         if le_dec (u_b b1) mm
         then size + (u_b b1) - mm
         else size).


  Definition shiftL (m : nat) : bounds + {BoundError} :=
    if lt_dec (size - m) (u_b b1)
    then error Overflow
    else ofc ((l_b b1) + m, (u_b b1) + m).

  Definition shiftR (m : nat) : bounds + {BoundError} :=
    ofc (max ((l_b b1) - m) 0, max ((u_b b1) - m) 0).

End BoundedOperations.
