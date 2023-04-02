Require Import Verse.
Require Import Verse.CryptoLib.curve25519.c.field.
Require Import Verse.CryptoLib.curve25519.c.portable.

Module Internal.
  (* Expose the field operations for testing *)

  Section Params.
    Variable progvar : VariableT.

    Definition LimbArray := Array nLimbs hostE Word64.
    Variable aLA : progvar of type LimbArray.
    Variable a b c : progvar of type Element.
    Section LoadStoreAll.

      Definition loadAndStore (aL bL : feVar progvar)
        : code progvar :=
        List.concat [ field.Internal.loadAll a aL;
                      field.Internal.storeAll a aL
          ].

    End LoadStoreAll.

    Section Locals.
      Variable oper  : feVar progvar -> feVar progvar -> feVar progvar -> code progvar.
      Variable operA : feVar progvar -> feVar progvar -> code progvar.

      Program Definition Store (arr : progvar of type LimbArray) (limb : feVar progvar) : code progvar :=
        foreachLimb (fun i (_ : i < nLimbs) => [code| arr[i] := limb [i] |]).

      Variable aL bL cL : feVar progvar.



      Definition fieldOp : code progvar :=
        List.concat [ field.Internal.loadAll b bL;
                      field.Internal.loadAll c cL;
                      oper aL bL cL;
                      Store aLA aL
          ].


      Definition fieldOpAssign : code progvar :=
        List.concat [ field.Internal.loadAll b bL;
                      operA aL bL;
                      Store aLA aL
          ].

    End Locals.

    Definition loadStore := do loadAndStore end.
    Definition addition  := do fieldOp add end.
    Definition addAssign := do fieldOpAssign addAssign end.

    Definition subtraction := do fun (B : progvar of type Word64) => fieldOp (field.sub B) end.
    Definition subAssign  := do fun (B : progvar of type Word64) => fieldOpAssign (field.subAssign B) end.
    Definition multiplication := do fieldOp mult end.

  End Params.

End Internal.

Inductive name :=
| verse_gf25519_load_store
| verse_gf25519_addition
| verse_gf25519_addition_assign
| verse_gf25519_minus
| verse_gf25519_minus_assign
| verse_gf25519_multiplication.


Require Import Verse.Target.C.
Require Import Verse.Error.

Definition loadAndStore : CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_gf25519_load_store (Internal.loadStore).
Defined.

Definition addition : CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_gf25519_addition (Internal.addition).
Defined.


Definition addAssign : CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_gf25519_addition_assign (Internal.addAssign).
Defined.


Definition subtraction : CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_gf25519_minus (Internal.subtraction).
Defined.


Definition subAssign : CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_gf25519_minus_assign (Internal.subAssign).
Defined.


Definition multiplication : CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_gf25519_multiplication (Internal.multiplication).
Defined.

Definition loadStore : Compile.programLine := recover loadAndStore.
Definition addF  : Compile.programLine := recover addition.
Definition addAF : Compile.programLine := recover addAssign.
Definition subF  : Compile.programLine := recover subtraction.
Definition subAF  : Compile.programLine := recover subAssign.
Definition multF  : Compile.programLine := recover multiplication.

Definition program := verseC [ loadStore;
                               addF;
                               addAF;
                               subF;
                               subAF;
                               multF
                        ]%list.


Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name} (name : Name)
  := mkProgram name [
         function verse_gf25519_load_store Internal.loadAndStore;
         function verse_gf25519_addition Internal.addition ;
         function verse_gf25519_addition_assign Internal.addAssign;
         function verse_gf25519_minus Internal.subtraction;
         function verse_gf25519_minus_assign Internal.subAssign;
         function verse_gf25519_multiplication Internal.multiplication
       ].
