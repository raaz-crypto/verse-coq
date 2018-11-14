Require Import Verse.Language.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Error.
Require Import Verse.Word.
Require Import Verse.DecFacts.
Require Import Verse.Semantics.Store.

Require Import Bvector.
Require Import Vector.
Require Import List.
Import ListNotations.
Import VectorNotations.

Set Implicit Arguments.

Generalizable All Variables.

Module Semantics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Module C  := ConstDenote W CW.
  Module OP := OpDenote W O.

  Import OP.

  Section Semantics.

    Variable s : Store.

    Let store := store s.
    Let v := v s.
    Let eval := eval s.
    Let storeUpdate := storeUpdate s.

    Section InstructionDenote.

      (* Extracts from the context v the value denoted by an arg *)

      Definition argDenote (S : store)
                 `{ty : type k} `(a : arg v aK ty)
      : @typeDenote TypeDenote _ _ ty :=
        match a in (arg _ _ ty) return typeDenote ty with
        | var av               => eval S _ av
        | Language.Ast.const c => C.constDenote c
        | index x i            => (fun y => nth_order y (proj2_sig i)) (eval S _ x)
        end.

      (* Auxiliary function to lift an arg value change to store *)
      Definition largUpdate `{ty : type k} (a : larg v ty)
                 (val : typeDenote ty : Type)
                 (S : store)
        : store :=
        match a in arg _ lval ty  return (typeDenote ty : Type)
                                         -> store
        with
        | @var _ lval _ _ av        => fun val' => storeUpdate _ av
                                                               (fun _ => val')
                                                               S
        | @index _ lval  _ _ _ x i => fun val' => storeUpdate _ x
                                                              (fun vec =>
                                                                 replace_order vec (proj2_sig i) val')
                                                              S
        end val.

      (* The constant 1 as a verse constant to provide an interpretation
         for the increment/decrement instructions
       *)
      Let one (ty : type direct) : constant ty :=
        match ty as ty' in type direct return constant ty' with
        | word n        => Nibble.Internal.fromNR _ 1
        | multiword _ _ => const (Nibble.Internal.fromNR _ 1) _
        end
      .

      Fixpoint  instructionDenote (i : instruction v) (S : store) {struct i}
        : (store) :=
        let updatePair `{ty : type k} (a1 a2 : larg v ty) val :=
            let S' := largUpdate a1 (fst val) S in largUpdate a2 (snd val) S' in
        match i with
        | increment la => largUpdate la (OP.opDenote _ plus
                                                     (argDenote S la)
                                                     (argDenote S (Ast.const (one _))))
                                     S
        | decrement la => largUpdate la (OP.opDenote _ minus
                                                     (argDenote S la)
                                                     (argDenote S (Ast.const (one _))))
                                     S
        | assign ass => match ass with
                        | extassign4 op la1 la2 ra1 ra2 ra3 =>
                          updatePair la1 la2 (OP.opDenote _ op
                                                          (argDenote S ra1)
                                                          (argDenote S ra2)
                                                          (argDenote S ra3))
                        | extassign3 op la1 la2 ra1 ra2     =>
                          updatePair la1 la2 (OP.opDenote _ op
                                                          (argDenote S ra1)
                                                          (argDenote S ra2))
                        | assign3 op la ra1 ra2 => largUpdate la (OP.opDenote _ op
                                                                              (argDenote S ra1)
                                                                              (argDenote S ra2))
                                                              S
                        | assign2 op la ra1     => largUpdate la (OP.opDenote _ op
                                                                              (argDenote S ra1))
                                                              S
                        | update2 op la ra1     => largUpdate la (OP.opDenote _ op
                                                                              (argDenote S la)
                                                                              (argDenote S ra1))
                                                              S
                        | update1 op la         => largUpdate la (OP.opDenote _ op
                                                                              (argDenote S la))
                                                              S
                        end
        | moveTo x ix ra => largUpdate (index x ix) (@argDenote S _ _ rval (var ra))
                                       S
        | clobber ra     => S
        end.


    End InstructionDenote.

    Section Annotate.

      (** The specification at any given program point carries
        along the assumptions made so far and the accumulated
        claims

        The specification at the end of the sequence:
                     ...
                     ASSUME A1
                     ...
                     CLAIM C1
                     ...
                     ASSUME A2
                     ...
                     CLAIM C2

        would be the pair -

                 (A1 /\ A2, (A1 -> C1) /\ (A1 /\ A2 -> C2))

        with the annotations being instantiated with the stores
        at the corresponding program points.
       *)

      Definition spec := (Prop * Prop)%type.

      Variable st : store.
      Variable ost : store.

      Definition annotationDenote (a : annotation v) (s : spec) : spec :=
        let (ass, cl) := s in
        let ctxtP := (eval st, eval ost) in
        (fun na => ((ass /\ na, cl /\ (ass -> na)))) (a ctxtP).

    End Annotate.

    Section CodeDenote.

      (* The Type capturing the program state *)
      Definition state := (store * store * spec)%type.

      Definition clDenote (cl : codeline v) (s : state) : state :=
        let '(st, ost, sp) := s in
        match cl with
        | assert a => (fun na => (st, ost, na)) (annotationDenote st ost a sp)
        | inst  i => (fun ni => (ni, ost, sp)) (instructionDenote i st)
        end.

      Definition codeDenote c s : state := List.fold_left
                                             (fun s i => (clDenote i) s)
                                             c
                                             s.
      (*
    Definition unchanged b : Prop := forall st `(ty : type k) (x : v ty),
        List.In (existT _ _ (existT _ _ x)) (changed b) \/
        (fst (fst st)) _ _ x = (fst (fst (codeDenote b st))) _ _ x.
       (* Try this with Ensembles *)
       *)

      Definition codeCheck c init : Prop :=
        (fun x => snd (snd x)) (codeDenote c (init, init, (True, True))).

      Definition SAT c    := forall init, codeCheck c init.

    End CodeDenote.

  End Semantics.

End Semantics.

Module StandardSemantics := Semantics StandardWord StandardConsts StandardWordOps.

Require Import Verse.Semantics.ScopeStore.

Module SemanticTactics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Module Export S := Semantics W CW O.

  Definition genSAT `(vT : Vector.t (some type) n) c
    := SAT (scopeStore vT) (@fillDummy (@code _) _ vT c).

  Let Fixpoint swapScope t (v : GenVariableT t)
      n (vT : Vector.t (some t) n) typ C {struct vT}
    : (scoped v vT (typ -> C)) -> (typ -> scoped v vT C) :=
    match vT with
    | []                             => id
    | ((existT _ _ ty) :: vTt)%vector => fun s x vty => swapScope _ _ _
                                                                  (s vty) x
    end.

  Let swapGScope (t : kind -> Type) n (vT : Vector.t (some t) n)
      typ (C : GenVariableT t -> Type)
    : (forall v, scoped v vT (typ -> C v)) -> typ -> forall v, scoped v vT (C v)
    := fun f => fun t v => (swapScope v vT (C v) (f v) t).

  Arguments swapGScope [_ n] _ [typ] _ _ /.

  Ltac scopeTys xt :=
    match xt with
    | _ ?y -> ?z => refine ((fun p => (((existT _ _ y) :: fst p, snd p))) _)%vector; scopeTys z
    | ?x         => exact ([]%vector, x)
    end.

  (* Extract the scope out of a generic function *)
  Ltac scopeAndInner x := let xt := type of (x ProxyVar) in scopeTys xt.

  Ltac rearrScope x :=
    let scp := fresh "scp" in
    let sc  := fresh "sc"  in
    let typ := fresh "typ" in
    let rx  := fresh "rx"  in
    (* Bring out the leading scope and the scoped Type *)
    simple refine (let scp : (Vector.t (some type) _ * Type) := _ in _);
    [shelve | scopeAndInner x | idtac];
    pose (sc := fst scp); simpl in *;
    let nx := fresh "nx" in
    tryif
      (* Swap out one inner parameter if possible *)
      pose (nx := swapGScope sc _ x)
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

  Ltac mapTyOf xt :=
    match xt with
    | _ ?y -> ?z => refine ((existT _ _ y) :: _)%vector; mapTyOf z
    | ?x         => exact ([]%vector)
    end.

  (* Extract the scope out of a generic function *)
  Ltac getScope x := let xt := type of (x ProxyVar) in mapTyOf xt.

  (* Recovers the specification corresponding to a code block
     as a Prop *)
  Ltac extractSAT func :=
    let sc := fresh "sc" in
    simple refine (let sc : Vector.t (some type) _ := _ in _);
    [shelve | getScope func | idtac];
    exact (genSAT sc func).

  (* Parametrize target Prop on non-variable parameters *)
  Ltac parametrize x :=
    repeat
      match type of x with
      | GenVariableT _ -> _ => extractSAT x
      | VariableT -> _      => extractSAT x
      | ?T -> _ => let t := fresh "t" in
                   refine (forall t : T, _ : Prop);
                   parametrize (x t)
      end.

  (* Final tactic to extract a Prop from an annotated code block
     with mixed scope *)
  Ltac exParamProp x :=
    let tmp := fresh "tmp" in
    simple refine (let tmp : _ := _ in _);
    [shelve | rearrScope x | idtac];
    simpl in tmp; parametrize tmp.

  (* Destruct the variable store for easier access to valuations *)
  Ltac breakStore :=
    repeat
      match goal with
      | a : _ * _ |- _ => simpl in a; destruct a
      | |- forall _ : _, _ => intro; simpl in * |-
      end.

  (* A starter to preface a proof attempt on a Prop extracted via
     extractSAT *)
  Ltac simplify :=
    repeat
      (match goal with
       | |- ?p              => unfold p
       | a : _ * _ |- _     => simpl in a; destruct a
       | |- forall _ : _, _ => intro
       | |- exists _ : _, _ => eapply ex_intro
       | |- _ /\ _          => constructor
       | |- _ = _           => constructor
       | _                  => simpl in *
       end; repeat autounfold).

End SemanticTactics.

Module StandardTactics := SemanticTactics StandardWord StandardConsts StandardWordOps.
