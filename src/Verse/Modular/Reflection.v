Require Import NArith.
Require Import Verse.Modular.Equation.

Create HintDb localdb.

Module Type Rep.
  Parameter rep : N -> Type.
  Parameter denote      : forall m : N, rep m -> N.
  Parameter normalise   : forall m : N, rep m -> rep m.
  Parameter normalise_spec : forall (M : N) (r : rep M), denote M r ≡ denote M (normalise M r) [mod M].
  Parameter const : forall m : N, N -> rep m.
  Parameter add : forall m : N, rep m -> rep m -> rep m.
  Parameter mul : forall m : N, rep m -> rep m -> rep m.
  Parameter modulo : forall m : N, rep m -> rep m.
  Parameter opp : forall m : N, rep m -> rep m.
  Parameter minus : forall m : N, rep m -> rep m -> rep m.
End Rep.

Module Reflect (R : Rep).

  Ltac reify e M :=
    match e with
    | (?e1 + ?e2)%N => let e1p := reify constr:(e1) M in
                      let e2p := reify constr:(e2) M in
                      constr:(R.add e1p e2p)
    | (?e1 * ?e2)%N => let e1p := reify constr:(e1) M in
                      let e2p := reify constr:(e2) M in
                      constr:(R.mul e1p e2p)
    | (?ep mod ?M)%N => let epp := reify ep M in
                       constr:(R.modulo M epp)
    | (oppMod ?M ?ep)  => let eq := reify ep M in
                        constr:(R.opp M eq)
    | (minusMod ?M ?e1 ?e2) => let e1p := reify constr:(e1) M in
                              let e2p := reify constr:(e2) M in
                              constr:(R.minus M e1p e2p)
    | _  => constr:(R.const M e)

    end.


  Ltac semantic_rewrite X eX
    := let H := fresh "HSem" in
       assert (H: X = R.denote _ eX) by (simpl; trivial);
       rewrite H.

  Ltac nf_rewrite eX M := modrewrite (R.normalise_spec M eX); simpl.

  Ltac nf X M :=
    let eX := reify X M in
    semantic_rewrite X eX;
    nf_rewrite eX M.

  Ltac normalise norm := match goal with
                         |  [ |- ?X ≡ ?Y [mod ?M] ]
                            =>  nf X M;
                               nf Y M; trivial
                         end.
End Reflect.
