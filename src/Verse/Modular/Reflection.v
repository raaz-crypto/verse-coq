Require Import NArith.
Require Import Verse.Modular.Equation.
Require Export setoid_ring.Algebra_syntax.

Class Rep (r : Type)
  `{Zero r}
  `{One  r}
  `{Addition r}
  `{Multiplication r r}
  `{Subtraction r}
  `{Opposite r}
  := { denote          : r -> N;
       const           : N -> r;
       characteristic  : N;
       const_spec  : forall n : N, denote (const n) ≡ n [mod characteristic]
  }.

Class Normalise (r : Type)`{Rep r}
  := { normalise : r -> r;
       normalise_spec : forall r, denote r ≡ denote (normalise r) [mod characteristic]
  }.

Ltac semantic_rewrite X eX
  := let H := fresh "HSem" in
     assert (H: X = denote eX) by (simpl; trivial);
     rewrite H.

Ltac nf_rewrite eX := modrewrite (normalise_spec eX); simpl.

Ltac nf reify X :=
  let eX := reify X in
  semantic_rewrite X eX;
  nf_rewrite eX.

Ltac normalise reify norm := match goal with
                             |  [ |- ?X ≡ ?Y [mod ?M] ]
                                =>  nf X M;
                                   nf Y M; trivial
                             end.





(*
Inductive Exp :=
| Const : N -> Exp
| Add   : Exp -> Exp -> Exp
| Mul   : Exp -> Exp -> Exp
| Sub   : Exp -> Exp -> Exp
| Mod   : Exp
| Opp   : Exp -> Exp.

Fixpoint expDenote {r : Type} `{Rep r}(e : Exp) : r :=
  match e with
  | Const n => const n
  | Add   e1 e2  => addition (expDenote e1) (expDenote e2)
  | Mul   e1 e2  => multiplication (expDenote e1)(expDenote e2)
  | Sub   e1 e2  => subtraction (expDenote e1) (expDenote e2)
  | Opp   ep     => opposite (expDenote ep)
  end.

Instance add_exp : Addition Exp := Add.
Instance mul_exp : Multiplication (A:=Exp)(B:=Exp) := Mul.
Instance opp_exp : Opposite

Ltac reify e r :=
  match e with
  | (addition ?e1 ?e2) => let e1p := reify constr:(e1) in
                         let e2p := reify constr:(e2) in
                         constr:(addition (A:=r) e1p e2p)
  | (multiplication ?e1 ?e2)%N => let e1p := reify constr:(e1) in
                                 let e2p := reify constr:(e2) in
                                 constr:(multiplication (A:=r)(B:=r) e1p e2p)
  | (opposite ?ep)  => let eq := reify ep in
                      constr:(opposite (A:=r) eq)
  | (subtraction ?e1 ?e2) => let e1p := reify constr:(e1) in
                            let e2p := reify constr:(e2) in
                            constr:(subtraction (A:=r) e1p e2p)
  | _  => constr:(const e)
  end.

 *)
