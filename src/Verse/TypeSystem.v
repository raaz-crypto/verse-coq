(** * Type Systems.

A generic types system for verse and its target languages. There are
two kinds of types -- direct types and the memory types. Direct types
are types whose values can reside directly in program variables (or
registers in the case of machines). Typically word types or SIMD
vector types are direct types. Memory types are those whose values are
accessed through indirect referencing. Examples for memory types are
arrays and pointers.


 *)

Inductive kind := direct | memory.

Structure typeSystem :=
  TypeSystem { typeOf       : kind -> Set;
               constOf      : typeOf direct -> Type;
             }.


(** ** Typed variables.

When building programming constructs, we need variables. In a typed
setting, we would like the variables to be parameterised by types. The
[VariableT ts] should be seen as the universe of program variables for
programs that use the type system [ts].

*)

Definition VariableT (ts : typeSystem) := forall k, forall ty : typeOf ts k, Set.


(** ** Translation between typed languages.

All our languages are typed. When compiling from one language to
another, we need translations of these types. Type maps are such
translations. We need to preserve typing which mapping constants.

 *)

Structure typeSystemMap
  := TypeSystemMap { dom      : typeSystem;
                     rng      : typeSystem;
                     mapType  : forall k, typeOf dom k -> typeOf rng k;
                     mapConst : forall ty, constOf dom ty -> constOf rng (mapType direct ty)
                   }.


Section SubType.

  Variable ts : typeSystem.
  Variable P : forall k, typeOf ts k -> Prop.

  Definition subSystem  :=
  let subType k := { ty : typeOf ts k | P k ty } in
  let subConst sty := match sty with
                      | exist _ ty _ => constOf ts ty
                      end
  in TypeSystem subType subConst.

  Definition liftType k ( tyS : typeOf subSystem k) : typeOf ts k :=
    let (ty0, _) := tyS in ty0.


  Definition liftConst
    : forall tyS : typeOf subSystem direct, constOf subSystem tyS -> constOf ts (liftType direct tyS)
    := fun tyS : typeOf subSystem direct =>
         match tyS as tyS0 return constOf subSystem tyS0 -> constOf ts (liftType direct tyS0) with
         | exist _ ty0 _  => fun x : constOf ts ty0 => x
         end.




End SubType.

Arguments subSystem [ts].
Arguments liftType   [ts].
Arguments liftConst  [ts].

Canonical Structure injection {ts} P := TypeSystemMap (subSystem P) ts (liftType P) (liftConst P).



(** It is not always possible to map the types in the source language
    to meaningful types in the target language. In such cases, we look
    at type maps which result in translation errors.
 *)

Inductive TranslationError : Prop :=
| CouldNotTranslate : forall A : Type, A -> TranslationError.

Arguments  CouldNotTranslate [A].

Definition translation ts0 ts1 := forall k, typeOf ts0 k -> typeOf ts1 k + { TranslationError }.

Require Import Verse.Error.
Definition domain {ts0 ts1}(tr : translation ts0 ts1) :=
  subSystem (fun k => InDomain (tr k)).


Definition range {ts0 ts1}(tr : translation ts0 ts1) :=
  subSystem (fun k => InRange (tr k)).


Definition domainToRange {ts0 ts1}(tr :translation ts0 ts1) k
  : typeOf (domain tr) k -> typeOf (range tr) k := (totalCore (tr k)).

Definition constTranslation {ts0 ts1} (tr : translation ts0 ts1) :=
  forall ty, constOf (domain tr) ty -> constOf (range tr) (domainToRange tr direct ty).

Definition TypeTranslation {ts0 ts1} (tr : translation ts0 ts1)(comp : constTranslation tr)
  := TypeSystemMap (domain tr)(range tr) (domainToRange tr) comp.
