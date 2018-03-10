Require Import Verse.Language.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.DecFacts.
Require Import Verse.Error.

Require Import Vector.

Set Implicit Arguments.


Module Semantics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Module T  := TypeDenote W.
  Module C  := ConstDenote W CW.
  Module OP := OpDenote W O.

  Section InstructionDenote.

    Variable v : VariableT.

    (* We need a decidable equality on v to be able to update state at specified variables *)
    Variable v_eq_dec : forall {k} {ty : type k} (v1 v2 : v ty), bool.

    (* Variable errors *)
    Inductive VariableError : Prop :=
    | InvalidatedAt : forall {k} (ty : type k), v ty -> instruction v -> VariableError
    | OperationError : O.OpError -> instruction v -> VariableError.

    Definition State := forall k (ty : type k), v ty -> T.typeDenote ty + {VariableError}.

    Inductive StateError : Prop :=
    | InvalidUse : forall {k} {ty : type k}, v ty -> instruction v -> instruction v -> StateError
    | OperatorError : O.OpError -> instruction v -> instruction v -> StateError.

    (* Extracts from Stat the value denoted by an arg *)
    Definition argDenote (S : State) {k} {ty : type k} {aK} (a : arg v aK _ ty) : T.typeDenote ty + {VariableError} :=
      match a in (arg _ _ _ ty) return T.typeDenote ty + {VariableError} with
      | var av           => S _ _ av
      | Language.Ast.const c => {- C.constDenote c -}
      | index x i        => (fun y => nth_order y (proj2_sig i)) <$> S _ _ x
      end.

    (* The pattern match for stateUpdate is too gory to be illuminating *)
    Definition stateUpdate k {ty : type k} (var : v ty) (f : T.typeDenote ty + {VariableError} -> T.typeDenote ty + {VariableError}) :
      State -> State.
      unfold State in *; intros; intros.
      destruct (kind_eq_dec k k0); subst.
      destruct (ty_eq_dec ty ty0); subst.
      destruct (v_eq_dec X0 var); subst.
      exact (f (X _ _ var)).               (* update according to f at var *)
      all: exact (X _ _ X0).               (* use initial state value at all other points *)
    Defined.

    (* Auxiliary function to lift an arg value change to State *)
    Definition largUpdate {k} {ty : type k} (a : larg v _ ty) (val : T.typeDenote ty + {VariableError}) (S : State) : State :=
      match a in arg _ lval _ ty  return T.typeDenote ty + {VariableError} -> State with
      | @var _ lval _ _ av        => fun val' => stateUpdate av
                                                             (fun _ => val')
                                                             S
      | @index _ lval _ _ _ _ x i => fun val' => stateUpdate x
                                                             (fun vec =>
                                                                X <- vec; replace_order X (proj2_sig i) <$> val')
                                                             S
      end val.

    Definition instructionDenote (i : instruction v) (S : State) : State + {StateError} :=
      let pushErr Err T (p : T * T + {Err}) := match p with
                                              | {- (a, b) -} => ({- a -}, {- b -})
                                              | error e      => (error e, error e)
                                              end in
      let liftOpErr {T} (v : T + {O.OpError}) := match v with
                                                 | {- v -} => {- v -}
                                                 | error e => error (OperationError e i)
                                                 end in
      (* Auxiliary function to update arg values only when Valid *)
      let validate {k} {ty : type k} (a : larg v _ ty) val S :=
          match val with
          | {- oval -} => {- largUpdate a (liftOpErr oval) S -}
          | error e => error (match e with
                              | InvalidatedAt v iAt => InvalidUse v iAt i
                              | OperationError oe iAt => OperatorError oe iAt i
                              end)
          end in
      let validatePair {k} {ty : type k} (a1 a2 : larg v _ ty) val :=
          let '(val1, val2) := pushErr _ _ val in
          S' <- validate a1 val1 S; validate a2 val2 S' in

      match i with
      | assign ass => match ass with
                      | extassign4 op la1 la2 ra1 ra2 ra3 =>
                        validatePair la1 la2 (OP.opDenote _ op
                                                          <$> (argDenote S ra1)
                                                          <*> (argDenote S ra2)
                                                          <*> (argDenote S ra3))
                      | extassign3 op la1 la2 ra1 ra2     =>
                        validatePair la1 la2 (OP.opDenote _ op
                                                          <$> (argDenote S ra1)
                                                          <*> (argDenote S ra2))
                      | assign3 op la ra1 ra2 => validate la (OP.opDenote _ op
                                                                          <$> (argDenote S ra1)
                                                                          <*> (argDenote S ra2))
                                                          S
                      | assign2 op la ra1     => validate la (OP.opDenote _ op
                                                                          <$> (argDenote S ra1))
                                                          S
                      | update2 op la ra1     => validate la (OP.opDenote _ op
                                                                          <$> (argDenote S la)
                                                                          <*> (argDenote S ra1))
                                                          S
                      | update1 op la         => validate la (OP.opDenote _ op
                                                                          <$> (argDenote S la))
                                                          S
                      end
      | moveTo x ix ra => largUpdate (var ra)
                                     (error (InvalidatedAt ra i))
                                     <$>
                                     validate (index x ix) (inleft <$> (@argDenote S _ _ rval (var ra)))
                                     S
      | CLOBBER ra     => {- largUpdate (var ra)
                                        (error (InvalidatedAt ra i))
                                        S -}
      end.

  End InstructionDenote.

End Semantics.
