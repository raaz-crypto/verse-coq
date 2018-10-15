Require Import Verse.Language.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Error.
Require Import Verse.Word.

Require Import Bvector.
Require Import Vector.

Set Implicit Arguments.

Generalizable All Variables.

Module Semantics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Module C  := ConstDenote W CW.
  Module OP := OpDenote W O.

  Import OP.

  Section Store.
    Variable n : nat.
    Variable vT : Vector.t (some type) n.

    Let v := scopeVar vT.

    (* Data structure to encode the variable values for the structured
       ProxyVar variable type
    *)
    Definition store := allocation (fun _ ty => @typeDenote _ tyDenote _ ty + {contextErr}) vT.
    (* Omitting the implicit typeClass for `typeDenote` triggers a bug *)

  End Store.

  Arguments store [n] vT.

  (* Getting a variable value out of the store *)
  Fixpoint eval `{vT : Vector.t (some type) n} (s : store vT)
                `{ty : type k} (x : scopeVar vT ty)
    : @typeDenote _ tyDenote _ ty + {contextErr} :=
    match x in scopeVar vT0 ty0 return store vT0
                                       -> @typeDenote _ tyDenote _ ty0 + {contextErr} with
    | headVar _    => fun s0 => let '(vx, _) := s0 in vx
    | restVar _ rx => fun s0 => let '(_, st) := s0 in eval st rx
    end s.

  Fixpoint storeUpdate `(vT : Vector.t (some type) n)
                       `{ty : type k} (var : scopeVar vT ty)
    : (@typeDenote _ tyDenote _ ty + {contextErr} ->
       @typeDenote _ tyDenote _ ty + {contextErr}) ->
      store vT -> store vT :=
    match var as var0 in scopeVar vT0 ty0 return
          (@typeDenote _ tyDenote _ ty0 + {_}
           -> @typeDenote _ tyDenote _ ty0 + {_})
          -> store vT0 -> store vT0
    with
    | headVar _    => fun f s => let '(vx, st) := s in (f vx, st)
    | restVar _ rx => fun f s => let '(vx, st) := s in (vx, storeUpdate rx f st)
    end.


  Section InstructionDenote.

    Variable n  : nat.
    Variable vT : Vector.t (some type) n.

    (* Extracts from the store the value denoted by an arg *)

    Definition argDenote (S : store vT)
                         `{ty : type k} `(a : arg (scopeVar vT) aK ty)
      : @typeDenote _ tyDenote _ ty + {contextErr} :=
      match a in (arg _ _ ty) return @typeDenote _ tyDenote _ ty + {contextErr} with
      | var av           => eval S av
      | Language.Ast.const c => {- C.constDenote c -}
      | index x i        => (fun y => nth_order y (proj2_sig i)) <$> eval S x
      end.

    (* Auxiliary function to lift an arg value change to store *)
    Definition largUpdate `{ty : type k} (a : larg (scopeVar vT) ty)
                          (val : @typeDenote _ tyDenote _ ty + {contextErr})
                          (S : store vT)
      : store vT :=
      match a in arg _ lval ty  return @typeDenote _ tyDenote _ ty + {contextErr}
                                       -> store vT
      with
      | @var _ lval _ _ av        => fun val' => storeUpdate av
                                                             (fun _ => val')
                                                             S
      | @index _ lval  _ _ _ x i => fun val' => storeUpdate x
                                                         (fun vec =>
                                                            X <- vec;
                                                              replace_order X (proj2_sig i) <$> val')
                                                         S
      end val.

    (* The constant 1 as a verse constant to provide an interpretation
       for the increment/decrement instructions
    *)
    Let one (ty : type direct) : constant ty :=
      match ty as ty' in type direct return constant ty' with
      | word n        => bits (Ndigits.N2Bv_gen _ 1)
      | multiword _ _ => const (bits (Ndigits.N2Bv_gen _ 1)) _
      end
    .

    Fixpoint  instructionDenote (i : instruction (scopeVar vT)) (S : store vT) {struct i}
      : (store vT) + {contextErr} :=
      let pushErr `(p : T * T + {Err}) := match p with
                                          | {- (a, b) -} => ({- a -}, {- b -})
                                          | error e      => (error e, error e)
                                          end in
      let liftOpErr `(v : T + {O.OpError}) := match v with
                                              | {- v -} => {- v -}
                                              | error e => error Invalid
                                              end in
      (* Auxiliary functions to update arg values only when Valid *)
      let validate `{ty : type k} (a : larg (scopeVar vT) ty) val S :=
          match val with
          | {- oval -} => {- largUpdate a (liftOpErr oval) S -}
          | error e => error e
          end in
      let validatePair `{ty : type k} (a1 a2 : larg (scopeVar vT) ty) val :=
          let '(val1, val2) := pushErr val in
          S' <- validate a1 val1 S; validate a2 val2 S' in

      match i with
      | increment la => validate la (OP.opDenote _ plus
                                                 <$> (argDenote S la)
                                                 <*> (argDenote S (Ast.const (one _))))
                                 S
      | decrement la => validate la (OP.opDenote _ minus
                                                 <$> (argDenote S la)
                                                 <*> (argDenote S (Ast.const (one _))))
                                 S
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
                                     (error Invalid)
                                     <$>
                                     validate (index x ix) (inleft <$> (@argDenote S _ _ rval (var ra)))
                                     S
      | clobber ra     => {- largUpdate (var ra)
                                        (error Invalid)
                                        S -}
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

    Variable n : nat.
    Variable vT : Vector.t (some type) n.

    Variable st : store vT.

    Definition annotationDenote (a : annotation (scopeVar vT)) (s : spec) : spec + {contextErr}:=
      let (ass, cl) := s in
      match a with
      | assert a => (fun na => (ass /\ na, cl)) <$> a (@eval _ _ st)
      | claim  c => (fun nc : Prop => (ass, cl /\ (ass -> nc))) <$> c (@eval _ _ st)
      end.

  End Annotate.

End Semantics.

Module CodeSemantics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Module S := Semantics W CW O.
  Import S.

  Section CodeDenote.

    Variable n : nat.
    Variable vT : Vector.t (some type) n.

    (* The Type capturing the program state *)
    Let state := (store vT * spec)%type.

    Let clDenote (cl : codeline (scopeVar vT)) (s : state) : state + {contextErr} :=
      let (st, sp) := s in
      match cl with
      | annot a => (fun na => (st, na)) <$> annotationDenote st a sp
      | inst  i => (fun ni => (ni, sp)) <$> instructionDenote i st
      end.

    Definition codeDenote c init : Prop + {contextErr} :=
      (fun x => snd (snd x)) <$>
                             List.fold_left
                             (fun s i => bind s (clDenote i))
                             (@fillDummy (@code _) _ vT c)
                             {- (init, (True, True)) -}.

  End CodeDenote.

  Arguments codeDenote [n vT] _ _.

  Ltac mapTyOf xt :=
    match xt with
    | _ ?y -> ?z => refine ((existT _ _ y) :: _); mapTyOf z
    | _          => exact []
    end.

  (* Extract the scope out of a generic function *)
  Ltac getScope x := let xt := type of (x ProxyVar) in mapTyOf xt.

  Let addErr (Err : Prop) v1 `(vT : Vector.t (some type) n)
           (a : allocation v1 vT) :=
  mapAlloc v1 _ (fun _ _ => @inleft _ Err) _ a.

  (* Recovers the specification corresponding to a code block
     as a Prop or throws an error *)
  Ltac extractProp func :=
    let sc := fresh "sc" in
    simple refine (let sc : Vector.t (some type) _ := _ in _);
    [shelve | getScope func | idtac];
    let st := fresh "st" in
    refine (forall st : allocation (fun _ => typeDenote) sc, _ : Prop);
    let perr := fresh "perr" in
    simple refine (let perr : Prop + {contextErr} := _ in _);
    [ exact (@codeDenote _ sc func (addErr contextErr _ _ st)) | idtac ];
    exact (recover perr).

  (* A starter to preface a proof attempt on a Prop extracted via
     extractProp *)
  Ltac simplify :=
    repeat
      match goal with
      | |- ?p              => unfold p
      | |- forall _ : _, _ => intro
      | a : _ * _ |- _    => destruct a
      | _                  => simpl in *
      end.

End CodeSemantics.
