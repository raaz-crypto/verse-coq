Require Import Verse.
Require Import Syntax.
Require Import Language.
Require Import Types.
Require Import Types.Internal.
Require Import Arch.
Require Import Compile.
Require Import Word.
Require Import Error.
Require Import PrettyPrint.
Require Import DecFacts.
Require Import Language.Ast.

(* Require Import SeqFunction. *)

Require Basics.
Require Import Equality.
Require Import ListDec.
Require Import Omega.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Ensembles.
Require Vector.
Import VectorNotations.
Require Vectors.Fin.
Require Import Bool.
Set Implicit Arguments.

Close Scope vector_scope.

Inductive xRegName := reg_a | reg_b | reg_c | reg_d | reg_di | reg_si
                      | reg_r8 | reg_r9 | reg_r10 | reg_r11 | reg_r12 | reg_r13 | reg_r14 | reg_r15.
(*                      | reg_r (n : Fin.t 8) : xRegName.*)

Hint Resolve Fin.eq_dec : decidable_prop.
Lemma xRegName_eq_dec : eq_dec xRegName.
  destruct A1; destruct A2; crush_eq_dec.
Defined.

Hint Resolve xRegName_eq_dec : decidable_prop.

Inductive xreg : VariableT :=
| xr (_ : xRegName) (k : kind) (ty : type k)  : xreg ty
(*| xrH (_ : xRegName) : xreg Word8*)
.

(**** Consider moving xrL out too *)

Definition xreg_eqb {k} (ty : type k) (x1 x2 : xreg ty) : bool :=
  match x1, x2 with
  | xr n1 _, xr n2 _ => if xRegName_eq_dec n1 n2 then true else false
(*  | xrH r1, xrH r2     => if xRegName_eq_dec r1 r2 then true else false
  | _, _               => false*)
  end.

Lemma xreg_eqb_eq{k} (ty : type k) (x1 x2 : xreg ty) : xreg_eqb x1 x2 = true <-> x1 = x2.
  Hint Unfold xreg_eqb.
  dependent destruction x1; dependent destruction x2.
  crush_eq_dec;
  crush_eqb_eq.
Qed.

Tactic Notation "fill_ineq" uconstr(B) := (refine B; omega).

Notation al := (xr reg_a Word8).
Notation ax := (xr reg_a Word16).
Notation eax := (xr reg_a Word32).
Notation rax := (xr reg_a Word64).

Notation dl := (xr reg_d Word8).
Notation dx := (xr reg_d Word16).
Notation edx := (xr reg_d Word32).
Notation rdx := (xr reg_d Word64).

Inductive xvar : VariableT :=
| inRegister     : forall k (ty : type k), xreg ty -> xvar ty
| paramStack     : forall k (ty : type k), nat -> xvar ty
| localStack     : forall k (ty : type k), nat -> xvar ty
.

Record xFrame := { xFunctionName : string;
                   numParams      : nat;
                   usedReg       : list xRegName;
                   stackOffset   : nat }.

Module X86 <: ARCH.

  (** Name of the architecture family *)

  Definition name : string := "X86-64".

  (** The registers for this architecture *)

  Definition register := xreg.

  Definition machineVar := xvar.

  Definition HostEndian := littleE.

  Definition Word := Word64.

  Definition embedRegister := inRegister.

  Inductive typesSupported : forall k, Ensemble (type k) :=
  | uint8             : typesSupported Word8
  | uint16            : typesSupported Word16
  | uint32            : typesSupported Word32
  | uint64            : typesSupported Word64
  | xarray {a n e ty} : typesSupported ty -> typesSupported (array a n e ty)
  .

  Fixpoint typeCheck {k}(ty : type k) : {typesSupported ty} + {~ typesSupported ty}.
    refine (match ty with
            | word 0 | word 1 | word 2 | word 3  => left _
            | array a n e typ => match @typeCheck direct typ with
                               | left proof      => left (xarray proof)
                               | right disproof  => right _
                               end
            | _ => right _
            end
           ); repeat constructor; inversion 1; apply disproof; trivial.
  Defined.

  Definition supportedType := typesSupported.

  Definition isConst {k} {ty : type k} {aK} (a : arg machineVar aK _ ty) :=
    match a with
    | const _ => true
    | _       => false
    end.

  Definition isMem {ty : type direct} {aK} (a : arg machineVar aK _ ty) :=
    match a with
    | Ast.index _ _ => true
    | _           => false
    end.

  Let simple_binop  : list (simop binary) :=
    [plus; minus; bitOr; bitAnd; bitXor].

  Definition isRegister {k} {ty : type k} (r : xreg ty) :
    forall {k'} {ty' : type k'} {aK} (a : arg xvar aK _ ty'), bool.
    intros.
    destruct (kind_eq_dec k k'); [subst; destruct (ty_eq_dec ty ty'); [subst | ..] | ..].
    destruct a. destruct x. exact (xreg_eqb x r).
    all: exact false.
  Defined.

  Inductive isRegName (r : xRegName) :
    forall {k} {ty : type k} {aK}, arg xvar aK _ ty -> Prop :=
  | isRName : forall {k} (ty : type k) {aK}, isRegName r (@var _ aK _ _ (inRegister (xr r ty))).

  Lemma isRegName_dec rn {k} {ty : type k} {aK} (a : arg xvar aK _ ty) : decidable (isRegName rn a).
    destruct a as [ ? ? ? v | | ]; [ destruct v as [ ? ? r | | ] | .. ]; [ destruct r | ..];
    crush_eq_dec.
  Qed.

  Hint Resolve isRegName_dec : decidable_prop.

  Notation IsRegister reg arg := (isRegister reg arg = true).

  Definition onStack {k} {ty : type k} {aK} (a : arg machineVar aK _ ty) :=
    match a with
    | var (localStack _ _) | var (paramStack _ _) => true
    | _                  => false
    end.

  Definition supportedInst (i : instruction machineVar) :=
    match i with
    | assign (@update2 _ ty o a1 a2) =>  (List.In o simple_binop)
                                         /\ (ty = Word64 -> isConst a2 = false)       (* immediates not 64-bit *)
                                         /\ (isMem a1 = true -> isMem a2 = false)     (* both arguments cannot be memory *)
    | assign (@update1 _ ty o a)     => True
    | assign (@extassign3 _ ty exmul a1 a2 a3 a4) => (ty = Word64 -> isConst a4 = false)             (* immediates not 64-bit *)
(*                                                     /\ (ty = Word8 -> IsRegister ah a1 ->
                                                         IsRegister al a2 -> IsRegister al a3)       (* AH:AL <- AL * r/m 8 *)*)
                                                     /\ (ty <> Word8 -> isRegName reg_d a1 ->
                                                         isRegName reg_a a2 -> isRegName reg_a a3)   (* D:A   <- A  * r/m 16/32/64 *)
    | assign (@extassign4 _ ty eucl a1 a2 a3 a4 a5) => (ty = Word64 -> isConst a5 = false)           (* immediates not 64-bit *)
(*                                                       /\ (ty = Word8 -> IsRegister ah a1  -> IsRegister al a2
                                                           -> IsRegister ah a3 -> IsRegister al a4)  (* (AH,AL) <- AH:AL / r/m 8 *) *)
                                                       /\ (ty <> Word8 -> isRegName reg_d a1 -> isRegName reg_a a2 ->
                                                           isRegName reg_d a3 -> isRegName reg_a a4) (* (D,A)   <- D:A   / r/m 16/32/64 *)
    | assign (@assign2 _ ty nop a1 a2) => (ty = Word64 -> isConst a2 = true -> isMem a1 = false)
                                          /\ (isConst a2 = true -> isMem a1 = true -> isEndian xvar bigE a1 = false)
                                          /\ (isEndian xvar bigE a1 = true -> isMem a2 = false -> (ty = Word32 \/ ty = Word64) /\ onStack a2 = false)
                                          /\ (isEndian xvar bigE a1 = true -> isMem a2 = true -> isEndian xvar bigE a2 = true)
                                          /\ (isEndian xvar bigE a2 = true -> isMem a1 = true -> isEndian xvar bigE a1 = true)
    | @moveTo _ _ _ _ ty a i v => (@isEndian xvar lval _ _ bigE (Ast.index a i) = true ->
                                   (ty = Word32 \/ ty = Word64) -> @onStack _ _ rval (var v) = false)
    | CLOBBER v => @onStack _ _ rval (var v) = false
    | _ => False
    end.

  Definition instCheck i : decidable (supportedInst i).
    destruct i as [ a | x i | v ]; [ destruct a | .. ];
      simpl; (try destruct o); try solve_decidable.
  Defined.

  Definition functionDescription := xFrame.

End X86.

Module XFrame <: FRAME X86.

  Definition frameState := xFrame.

  Definition emptyFrame s :=
    {| xFunctionName := s;
       numParams     := 0;
       usedReg       := [];
       stackOffset   := 0
    |}.

  Definition iterateFrame (s : string) (ty : type memory) :=
    let state := {| xFunctionName := s;
                    numParams     := 2;
                    usedReg       := [reg_di; reg_si];
                    stackOffset   := 0
                 |} in
    _ <- when X86.typeCheck ty; {- (inRegister (xr reg_di ty), inRegister (xr reg_si X86.Word), state) -}.

  Definition CCregs : Vector.t xRegName 6 := [reg_di; reg_si; reg_d; reg_c; reg_r8; reg_r9]%vector.

  Let newParam state k (ty : type k) :=
    match lt_dec (numParams state) 6 with
    | left plt => let r := nth_order CCregs plt in
                  (inRegister (xr r ty),
                   {| xFunctionName := xFunctionName state;
                      numParams     := numParams state + 1;
                      usedReg       := r :: usedReg state;
                      stackOffset   := stackOffset state
                   |})
    | right _  => let ofst := 8 * (numParams state + 1 - 6 + 1) in
                  (paramStack ty ofst,
                   {| xFunctionName := xFunctionName state;
                      numParams     := numParams state + 1;
                      usedReg       := usedReg state;
                      stackOffset   := stackOffset state
                   |})
    end.

  Let newLocal state ty :=
    let ofst := stackOffset state + @sizeOf direct ty in
    (localStack ty ofst,
    {| xFunctionName := xFunctionName state;
       numParams     := numParams state;
       usedReg       := usedReg state;
       stackOffset   := ofst
    |}).


  Definition addParam state k ty :=
    _ <- when X86.typeCheck ty; {- @newParam state k ty -}.

  Definition stackAlloc state ty :=
    _ <- when X86.typeCheck ty; {- @newLocal state ty -}.

  Definition useRegister state (ty : type direct) (reg : xreg ty ):=
    match reg with
    | xr r ty =>
      if X86.typeCheck ty then
        if in_dec xRegName_eq_dec r (usedReg state)
        then None
        else Some
               {| xFunctionName := xFunctionName state;
                  numParams     := numParams state;
                  usedReg       := r :: usedReg state;
                  stackOffset   := stackOffset state
               |}
      else
        None
    end.

  Definition description := @id xFrame.

End XFrame.

Definition orig_reg := [reg_a; reg_b; reg_c; reg_d]%list.
Definition index_reg := [reg_di; reg_si]%list.
Definition new_reg := [reg_r8; reg_r9; reg_r10; reg_r11; reg_r12; reg_r13; reg_r14; reg_r15]%list.

Local Definition regName (r : xRegName) :=
  match r with
  | reg_a => text "a"
  | reg_b => text "b"
  | reg_c => text "c"
  | reg_d => text "d"
  | reg_di => text "di"
  | reg_si => text "si"
  | reg_r8 => text "r8"
  | reg_r9 => text "r9"
  | reg_r10 => text "r10"
  | reg_r11 => text "r11"
  | reg_r12 => text "r12"
  | reg_r13 => text "r13"
  | reg_r14 => text "r14"
  | reg_r15 => text "r15"
  end.

Local Definition origRegWrite k (ty : type k) d := match ty with
                                                   | Word8 => d <> text "l"
                                                   | Word16 => d <> text "x"
                                                   | Word32 => text "e" <> d <> text "x"
                                                   | Word64
                                                   | _      => text "r" <> d <> text "x"
                                                   end.

Local Definition indexRegWrite k (ty : type k) d := match ty with
                                                    | Word8 => d <> text "l"
                                                    | Word16 => d
                                                    | Word32 => text "e" <> d
                                                    | Word64
                                                    | _      => text "r" <> d
                                                    end.

Local Definition newRegWrite k (ty : type k) d := match ty with
                                                  | Word8 => d <> text "b"
                                                  | Word16 => d <> text "w"
                                                  | Word32 => d <> text "d"
                                                  | Word64
                                                  | _      => d
                                                  end.


Instance xRegPretty : forall k (ty : type k), PrettyPrint (xreg ty)
  := { doc := fun x => text "%" <> let 'xr r ty := x in
                                   let rd := regName r in
                                   if in_dec xRegName_eq_dec r orig_reg
                                   then origRegWrite ty rd
                                   else if in_dec xRegName_eq_dec r index_reg
                                        then indexRegWrite ty rd
                                        else newRegWrite ty rd
     }.

Instance xMachineVar : forall k (ty : type k), PrettyPrint (xvar ty)
  := { doc := fun x => match x with
                       | inRegister r           => doc r
                       | paramStack ty n        => decimal n <> paren (text "%ebp")
                       | localStack ty n        => text "-" <> decimal n <> paren (text "%ebp")
                       end
     }.

Local Definition xImm d := text "$" <> d.

Local Fixpoint xArgdoc {aK}{k}(ty : type k ) (av : arg xvar aK k ty) :=
  match av with
  | var v       => doc v
  | const c     => xImm (doc c)
  | Ast.index v (exist _ n _) => decimal (sizeOf ty * n) <> paren (doc v)
  end.

Instance arg_pretty_print : forall aK k ty, PrettyPrint (arg xvar aK k ty)
  := { doc := @xArgdoc _ _ ty }.


Local Definition iSuffix {k} (ty : type k) := match ty with
                                               | Word8 => text "b"
                                               | Word16 => text "w"
                                               | Word32 => text "l"
                                               | Word64 => text "q"
                                               | array _ _ _ _ => text "q"
                                               | _      => text "badType"
                                               end.

Local Definition xOp {la ra} (o : op la ra) {k} (ty : type k) := match o with
                                               | plus    => text "add"
                                               | minus   => text "sub"
                                               | mul     => text "imul"
                                               | exmul   => text "mul"
                                               | quot    => text "BadOp"
                                               | rem     => text "BadOp"
                                               | eucl    => text "div"
                                               | bitOr   => text "or"
                                               | bitAnd  => text "and"
                                               | bitXor  => text "xor"
                                               | bitComp => text "not"
                                               | rotL n  => text "rol"
                                               | rotR n  => text "ror"
                                               | shiftL n => text "shl"
                                               | shiftR n => text "shr"
                                               | nop     => text "mov"
                                                  end <> iSuffix ty.

Local Definition biargs d1 d2 := commaSep [d1; d2].

Local Definition mkInst i a := i <_> a.

Local Definition bswap {k} (ty : type k) (x : xreg ty) :=
  mkInst (text "bswap" <> iSuffix ty) (doc x).

Local Definition move {ty : type direct} (la : larg _ direct ty) (ra : rarg _ direct ty) :=
  let NOP := xOp nop ty in
  match la with
  | @Ast.index _ _ _ _ bigE _ _ _ => match ra, ty with
                                      | var (inRegister x), Word32
                                      | var (inRegister x), Word64 => vcat [ bswap x;
                                                                               mkInst NOP (biargs (doc ra) (doc la)) ]
                                      | @Ast.index _ _ _ _ bigE _ _ _, _ => mkInst NOP (biargs (doc ra) (doc la))
                                      | _, _ => text "badInst"
                                      end
  | var (inRegister x) => match ra, ty with
                          | @Ast.index _ _ _ _ bigE _ _ _, Word32
                          | @Ast.index _ _ _ _ bigE _ _ _, Word64 => vcat [ mkInst NOP (biargs (doc ra) (doc la));
                                                                             bswap x ]
                          | _, _ => mkInst NOP (biargs (doc ra) (doc la))
                          end
  | _                  => mkInst NOP (biargs (doc ra) (doc la))
  end.

Local Definition store {ty : type direct} (la : larg _ direct ty) (ra : rarg _ direct ty) :=
  vcat ([ move la ra ] ++
                       match ra with
                       | var (inRegister x) => match la with
                                               | @Ast.index _ _ _ _ bigE _ _ _ => [bswap x]
                                               | _ => []
                                               end
                       | _ => []
                       end).

Instance xAssignmentPrint : PrettyPrint (assignment xvar)
  := { doc := fun assgn => match assgn with
                           | @update2 _ ty op la ra => xOp op ty <_> biargs (doc ra) (doc la)
                           | @update1 _ ty op la    => xOp op ty <_> match op with
                                                                  | bitComp => doc la
                                                                  | rotL n
                                                                  | rotR n
                                                                  | shiftL n
                                                                  | shiftR n => biargs (xImm (decimal n)) (doc la)
                                                                  | nop => biargs (doc la) (doc la)
                                                                     end
                           | @assign2 _ ty nop la ra => move la ra
                           | _ => text "badInst"
                           end
     }.


Global Instance instruction_C_print : PrettyPrint (instruction xvar)
  := { doc := fun i => match i with
                       | assign a => doc a
                       | moveTo x i y => move (Ast.index x i) (var y)
                       | CLOBBER a     => empty
                       end
     }.

Module xCodeGen <: CODEGEN X86.

  Import X86.

  Definition emit (i : instruction xvar) : Doc + { not (supportedInst i) } :=
    _ <- when instCheck i; {- doc i -}.

  Definition sequenceInstructions ds := line <> vcat ds <> line.

  Let preamble n := [  text ".text";
                       text ".globl" <_> n;
                       text ".type" <_> n <> text ", @function";
                       empty;
                       n <> text ":" ].

  Let BP := text "%rbp".
  Let SP := text "%rsp".
  Let push r := mkInst (text "push" <> iSuffix Word) r.
  Let pop r  := mkInst (text "pop" <> iSuffix Word) r.

  Let setupBP := [ push BP;
                   mkInst (xOp nop Word) (biargs SP BP) ].

  Let allocStack n := if nat_eq_dec n 0 then [] else [mkInst (xOp minus Word) (biargs (xImm (decimal n)) SP)].
  Let preserveRegs l := map (fun n => push (doc (xr n Word))) l.
  Let restoreRegs l := map (fun n => pop (doc (xr n Word))) l.
  Let clearStack n := if nat_eq_dec n 0 then [] else [mkInst (xOp plus Word) (biargs (xImm (decimal n)) SP)].

  Let restoreBP := [mkInst (text "popq") BP].

  Let ret := [text "ret"].

  Let calleeSave := [reg_b; reg_r12; reg_r13; reg_r14; reg_r15].
  Let toSave l := filter (fun r => if in_dec xRegName_eq_dec r calleeSave then true else false) l.
  Let xComment s := text "#" <_> text s.

  Definition makeFunction state body := let ofst := stackOffset state in
                                        let name := text (xFunctionName state) in
                                        let regs :=  toSave (usedReg state) in
                                        vcat ((preamble name) ++
                                                              [nest 4 (vcat ([empty; xComment "Stack setup"] ++
                                                                             setupBP ++ allocStack ofst ++
                                                                             [xComment "Callee saved registers"] ++
                                                                             preserveRegs regs ++
                                                                             [body;
                                                                              xComment "Stack cleanup"] ++
                                                                             clearStack ofst ++
                                                                             [xComment "Restore registers"] ++
                                                                             restoreRegs regs ++ restoreBP ++
                                                                             ret))]).

  Definition loopWrapper (msgTy : type memory) (v : machineVar msgTy) (n : machineVar Word) (d : Doc) : Doc :=
    let label := text ".loopstart" in
    let iterate := [ doc (mkInst (xOp plus Word) (biargs (xImm (decimal (sizeOf msgTy))) (doc v)));
                     mkInst (text "dec" <> iSuffix Word) (doc n);
                     mkInst (text "jnz") label ] in
    vcat ([label <> text ":"] ++ [nest 4 d] ++ iterate).

End xCodeGen.

Module Compile := Compiler X86 XFrame xCodeGen.