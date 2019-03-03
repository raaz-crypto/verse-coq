Require Import Verse.Language.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Error.
Require Import Verse.Word.
Require Import Verse.DecFacts.
Require Import Verse.Semantics.Store.
Require Import Verse.Nibble.

Require Import NArith.
Require Import Bvector.
Require Import Vector.
Require Import List.
Import ListNotations.
Import VectorNotations.

Set Implicit Arguments.

Generalizable All Variables.

Module Semantics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Export O.
  Module C  := ConstDenote W CW.
  Module OP := OpDenote W O.

  Infix "+" := (O.wordOpDenote _ plus) : semantic_scope.
  Infix "-" := (O.wordOpDenote _ minus) : semantic_scope.
  Infix "*" := (O.wordOpDenote _ mul) : semantic_scope.
  Infix "/" := (O.wordOpDenote _ quot) : semantic_scope.
  Infix "mod" := (O.wordOpDenote _ rem) (at level 40) : semantic_scope.
  Infix "AND" := (O.wordOpDenote _ bitAnd) (at level 55) : semantic_scope.
  Infix "AND8" := (O.wordOpDenote 0 bitAnd) (at level 55) : semantic_scope.
  Infix "AND16" := (O.wordOpDenote 1 bitAnd) (at level 55) : semantic_scope.
  Infix "AND32" := (O.wordOpDenote 2 bitAnd) (at level 55) : semantic_scope.
  Infix "AND64" := (O.wordOpDenote 3 bitAnd) (at level 55) : semantic_scope.
  Infix "OR" := (O.wordOpDenote _ bitOr) (at level 60) : semantic_scope.
  Infix "OR8" := (O.wordOpDenote 0 bitOr) (at level 55) : semantic_scope.
  Infix "OR16" := (O.wordOpDenote 1 bitOr) (at level 55) : semantic_scope.
  Infix "OR32" := (O.wordOpDenote 2 bitOr) (at level 55) : semantic_scope.
  Infix "OR64" := (O.wordOpDenote 3 bitOr) (at level 55) : semantic_scope.
  Infix "XOR" := (O.wordOpDenote _ bitXor) (at level 57) : semantic_scope.
  Infix "XOR8" := (O.wordOpDenote 0 bitXor) (at level 55) : semantic_scope.
  Infix "XOR16" := (O.wordOpDenote 1 bitXor) (at level 55) : semantic_scope.
  Infix "XOR32" := (O.wordOpDenote 2 bitXor) (at level 55) : semantic_scope.
  Infix "XOR64" := (O.wordOpDenote 3 bitXor) (at level 55) : semantic_scope.
  Notation "'NOT' X" := (O.wordOpDenote _ bitComp X) (at level 40) : semantic_scope.
  Infix "NOT8" := (O.wordOpDenote 0 bitComp) (at level 55) : semantic_scope.
  Infix "NOT16" := (O.wordOpDenote 1 bitComp) (at level 55) : semantic_scope.
  Infix "NOT32" := (O.wordOpDenote 2 bitComp) (at level 55) : semantic_scope.
  Infix "NOT64" := (O.wordOpDenote 3 bitComp) (at level 55) : semantic_scope.

  Notation "X 'ShiftL' s" := (O.wordOpDenote _ (shiftL s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftL8' s" := (O.wordOpDenote 0 (shiftL s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftL16' s" := (O.wordOpDenote 1 (shiftL s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftL32' s" := (O.wordOpDenote 2 (shiftL s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftL64' s" := (O.wordOpDenote 3 (shiftL s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftR' s" := (O.wordOpDenote _ (shiftR s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftR8' s" := (O.wordOpDenote 0 (shiftR s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftR16' s" := (O.wordOpDenote 1 (shiftR s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftR32' s" := (O.wordOpDenote 2 (shiftR s) X) (at level 50) : semantic_scope.
  Notation "X 'ShiftR64' s" := (O.wordOpDenote 3 (shiftR s) X) (at level 50) : semantic_scope.
  Notation "X 'RotL' s" := (O.wordOpDenote _ (rotL s) X) (at level 50) : semantic_scope.
  Notation "X 'RotL8' s" := (O.wordOpDenote 0 (rotL s) X) (at level 50) : semantic_scope.
  Notation "X 'RotL16' s" := (O.wordOpDenote 1 (rotL s) X) (at level 50) : semantic_scope.
  Notation "X 'RotL32' s" := (O.wordOpDenote 2 (rotL s) X) (at level 50) : semantic_scope.
  Notation "X 'RotL64' s" := (O.wordOpDenote 3 (rotL s) X) (at level 50) : semantic_scope.
  Notation "X 'RotR' s" := (O.wordOpDenote _ (rotR s) X) (at level 50) : semantic_scope.
  Notation "X 'RotR8' s" := (O.wordOpDenote 0 (rotR s) X) (at level 50) : semantic_scope.
  Notation "X 'RotR16' s" := (O.wordOpDenote 1 (rotR s) X) (at level 50) : semantic_scope.
  Notation "X 'RotR32' s" := (O.wordOpDenote 2 (rotR s) X) (at level 50) : semantic_scope.
  Notation "X 'RotR64' s" := (O.wordOpDenote 3 (rotR s) X) (at level 50) : semantic_scope.

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
        | assign ass
          => match ass with
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

      Record state := { start  : store;
                        curr   : store;
                        lemmas : Prop;
                        spec   : Prop
                      }.

      Definition annotationDenote (a : annotation v) (s : state) : state :=
        let ctxtP := (eval (curr s), eval (start s)) in
        {| start := start s;
           curr  := curr  s;
           lemmas := lemmas s /\ a ctxtP;
           spec   := spec s /\ (lemmas s -> a ctxtP)
        |}.

    End Annotate.

    Section CodeDenote.

      (* The Type capturing the program state *)

      Definition clDenote (cl : codeline v) (s : state) : state :=
        match cl with
        | assert a => annotationDenote a s
        | inst  i => {| start := start s;
                        curr  := instructionDenote i (curr s);
                        lemmas := lemmas s;
                        spec   := spec s
                     |}
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
        spec (codeDenote c {| start := init;
                              curr  := init;
                              lemmas := True;
                              spec   := True
                           |}
             ).

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
    | []                          => id
    | ((existT ty) :: vTt)%vector => fun s x vty => swapScope _ _ _
                                                              (s vty) x
    end.

  Let swapGScope (t : kind -> Type) n (vT : Vector.t (some t) n)
      typ (C : GenVariableT t -> Type)
    : (forall v, scoped v vT (typ -> C v)) -> typ -> forall v, scoped v vT (C v)
    := fun f => fun t v => (swapScope v vT (C v) (f v) t).

  Arguments swapGScope [_ n] _ [typ] _ _.

  Ltac mapTyOf xt :=
    match xt with
    | ProxyVar ?y -> ?z => refine ((existT y) :: _)%vector; mapTyOf z
    | ?x         => exact ([]%vector)
    end.

  (* Extract the scope out of a generic function *)
  Ltac getScope x := let xt := type of (x ProxyVar) in mapTyOf xt.

  Ltac rearrScope x :=
    let scp := fresh "scp" in
    let sc  := fresh "sc"  in
    let typ := fresh "typ" in
    let rx  := fresh "rx"  in
    (* Bring out the leading scope and the scoped Type *)
    simple refine (let scp : Vector.t (some type) _ := _ in _);
    [shelve | getScope x | idtac];
    simpl in *;
    let nx := fresh "nx" in
    tryif
      (* Swap out one inner parameter if possible *)
      pose (nx := swapGScope scp _ x)
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

  Ltac simplify := repeat match goal with
                          | |- forall _ : Store.store _, _ =>
                            breakStore;
                            lazy -[RotRW RotLW ShiftRW ShiftLW XorW AndW OrW NegW
                                   fromNibbles
                                   numBinOp numUnaryOp numBigargExop numOverflowBinop
                                   Nat.add Nat.sub Nat.mul Nat.div Nat.pow
                                   N.add N.sub N.mul N.div N.div_eucl N.modulo
                                   Ox nth replace];
                            repeat
                              (match goal with
                               | |- _ /\ _          => constructor
                               | |- _ -> _          => intro
                               | H : _ /\ _ |- _    => destruct H
                               | H : True |- _      => clear H
                               | |- True            => constructor
                               | |- ?x = ?x         => trivial
                               | H : True |- _      => clear H
                               | H : unit |- _      => clear H
                               end)
                          | |- forall _, _ => intro
                          | |- ?I          => unfold I; unfold genSAT; unfold SAT
                          end.
(*
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
*)
End SemanticTactics.

Module StandardTactics := SemanticTactics StandardWord StandardConsts StandardWordOps.
