Require Import Verse.
Require Import BinNat.
Require Import Arith.
Require Import Verse.CryptoLib.curve25519.c.field.
Import List.ListNotations.
(** * Curve 25519 and its parameters *)



Definition Word      := Word64.
Definition Element   := (Array 4 littleE Word).
Definition Scalar    := (Array 4 littleE Word).

Module Internal.

  Section Clamping.
    Variable progvar : VariableT.

    (** ** Clamping the scalar [n].

        The elliptic curve secret consists of computing [n Q] for the
        base point [Q]. To ensure that the [nQ] falls into the
        appropriate prime order subgroup of Curve25519 group we need
        to clamp n appropriately.

     *)


    Definition clamp (T : progvar of type Word) (scalA : progvar of type Scalar) : code progvar.
      verse [code|
          T := scalA[ 0 ];
          T &= `Ox "ff:ff:ff:ff ff:ff:ff:f8"`;
          scalA[ 0 ] <- T;

          T := scalA[ 3 ];
          T &= `Ox "7f:ff:ff:ff ff:ff:ff:ff"`;
          T |= `Ox "40:00:00:00 00:00:00:00"`;
          scalA[ 3 ] <- T
        |].
    Defined.

    Definition clampIter (T : progvar of type Word) : iterator progvar Scalar
      := {| setup    := [];
            process  := clamp T;
            finalise := []
         |}%list.

    Definition ClampIter := do clampIter end.


  End Clamping.

  (** ** The X25519 function.

  Given a scalar [n] and the X coordinate a point X(P) of the point P
  on the elliptic curve curve25519, the X25519 function computes the
  X-coordinate X (n P) coordinates the point [n P]. So the parameters
  for the function are.


   *)

  Section Params.
    Variable progvar : VariableT.
    Context (scalar :  progvar of type Scalar)(point : progvar of type Element).
    Program Definition scalarWord i (_ : i < 4) : lexpr progvar of type Word := [verse| scalar [i] |].
    Section Locals.

      Definition propagateTwice (x : feVar progvar) : code progvar := (propagate x ++ propagate x)%list.

      (** * Computational representations.

      The local variables are essentially the computational
      representations of the various field elements as limbs. It also
      have some temporary variables.

       *)


      (* Base point *)
    Variable xB : feVar progvar.

    Definition LoadBasePoint : code progvar := field.Internal.loadAll point xB.
    (* Point P *)
    Variable x2 z2 : feVar progvar.
    Variable x3 z3 : feVar progvar.


    Definition initialize : code progvar :=
      List.concat [ field.Internal.loadAll point xB;

                    field.setFeVar x2 feOne;
                    field.setFeVar z2 feZero;

                    field.copyFeVar x3 xB;
                    field.setFeVar z3 feOne
        ]%list.

    Variable t0 t1 t2 t3 : feVar progvar.

    (** Temporary variable need by subtraction *)
    Variable B255 : progvar of type Word64.
    Definition subtract := field.sub B255.
    Definition subtractAssign := field.subAssign B255.

    (**

       Optimised Montgomery formula: The table here is taken from the formula.org file
       where you can see a fuller explanation.


| Value                         | SSA | SSA program      | Need | x₂  | x₃  | z₂  | z₃  | t₀  | t₁  | Inst             | size | Req size | Carry |
|-------------------------------+-----+------------------+------+-----+-----+-----+-----+-----+-----+------------------+------+----------+-------|
| a                             |   0 | v₀ = a           |    5 | v₀  |     |     |     |     |     |                  |   40 | 40       |     0 |
| b                             |   1 | v₁ = b           |    7 |     | v₁  |     |     |     |     |                  |   40 | 40       |     0 |
| c                             |   2 | v₂ = c           |    5 |     |     | v₂  |     |     |     |                  |  std | std      |     0 |
| d                             |   3 | v₃ = d           |    7 |     |     |     | v₃  |     |     |                  |  std | std      |     0 |
| a + c                         |   4 | v₄ = v₀ + v₂     |    9 |     |     |     |     | v₄  |     | t₀ = x₂ + z₂     |   42 | std      |     1 |
| a - c                         |   5 | v₅ = v₀ - v₂     |   11 | v₅  |     |     |     |     |     | x₂ -= z₂         |   42 | std      |     1 |
| b + d                         |   6 | v₆ = v₁ + v₃     |   10 |     |     |     |     |     | v₆  | t₁ = x₃ + z₃     |   42 | std      |     1 |
| b - d                         |   7 | v₇ = v₁ - v₃     |    8 |     | v₇  |     |     |     |     | x₃ -= z₃         |   42 | std      |     1 |
| (a + c)(b - d)                |   8 | v₈ = v₄ * v₇     |   13 |     |     |     | v₈  |     |     | z₃ = x₃ * t₀     |   61 | 40       |     1 |
| (a + c)²                      |   9 | v₉ = v₄²         |   18 |     |     | v₉  |     |     |     | z₂ = t₀²         |   61 | std      |     2 |
| (a - c)(b + d)                |  10 | v₁₀ = v₅ * v₆    |   13 |     | v₁₀ |     |     |     |     | x₃ = x₂ * t₁     |   61 | std      |     2 |
| (a - c)²                      |  11 | v₁₁ = v₅²        |   16 |     |     |     |     |     | v₁₁ | t₁ = x₂²         |   61 | std      |     2 |
| 2(ab - cd)                    |  12 | v₁₂ = v₈ + v₁₀   |   21 |     |     |     |     | v₁₂ |     | t₀ = z₃ + x₃     |   41 | std      |     1 |
| 2(bc - ad)                    |  13 | v₁₃ = v₈ - v₁₀   |   14 |     |     |     | v₁₃ |     |     | z₃ -= x₃         |   41 | std      |     1 |
| 4(bc - ad)²                   |  14 | v₁₄ = v₁₃²       |   20 |     | v₁₄ |     |     |     |     | x₃ = z₃²         |   61 | std      |     2 |
| (a² - c²)²           = X₂ᵢ    |  15 | v₁₅ = v₉ * v₁₁   |    ∞ | v₁₅ |     |     |     |     |     | x₂ = z₂ * t₁     |   61 | 40       |     1 |
| 4ac                           |  16 | v₁₆ = v₉ - v₁₁   |   19 |     |     |     | v₁₆ |     |     | z₃ = z₂ - t₁     |   27 | 27       |     0 |
| 486660 ac = (A - 2)a c        |  17 | v₁₇ = 121665 v₁₆ |   18 |     |     |     |     |     | v₁₇ | t₁ = 121665 * z₃ |   44 | 44       |     0 |
| a² + A ac + c²                |  18 | v₁₈ = v₉ + v₁₇   |   19 |     |     |     |     |     | v₁₈ | t₁ += z₂         |   45 | std      |     1 |
| 4ac (a² + A ac + c²) = Z₂ᵢ    |  19 | v₁₉ = v₁₆ * v₁₈  |    ∞ |     |     | v₁₉ |     |     |     | z₂ = t₁ * z₃     |   61 | std      |     2 |
| 4 X(bc - ad)²        = 4Z₂ᵢ₊₁ |  20 | v₂₀ = v₁₄ * X(B) |    ∞ |     |     |     | v₂₀ |     |     | z₃ = x₃ * X(B)   |   61 | std      |     2 |
| 4 (ab - cd)²         = 4X₂ᵢ₊₁ |  21 | v₂₁ = v₁₂²       |    ∞ |     | v₂₁ |     |     |     |     | x₃ = t₀²         |   61 | 40       |     1 |
|-------------------------------+-----+------------------+------+-----+-----+-----+-----+-----+-----+------------------+------+----------+-------|


The size assumptions that we have are

1. [x2] [x3] are at most 41 bits (so one carry propagation will get them to standard form)
2. [z2] [z3] are in standard form.

     *)

    Definition Step : code progvar :=
      List.concat [
          add t0 x2 z2;           propagate t0;        (* std sized *)
          subtractAssign x2 z2;   propagate x2;        (* std sized *)
          add t1 x3 z3;           propagate t1;        (* std sized *)
          subtractAssign x3 z3;   propagate x3;        (* std sized *)
          mult z3 x3 t0;          propagate z3;        (* 40 bits   *)
          square z2 t0;           propagateTwice z2;   (* std sized *)
          mult x3 x2 t1;          propagateTwice x3;   (* std sized *)
          square t1 x2;           propagateTwice t1;   (* std sized *)
          add t0 z3 x3;           propagate t0;        (* 41 -> std sized *)
          subtractAssign z3 x3;   propagate z3;        (* 42 -> std sized *)
          square x3 z3;           propagateTwice x3;   (* std sized *)
          mult x2 z2 t1;          propagate  x2;       (* 61 -> 40 *)
          subtract z3 z2 t1;      (* no prop *)        (* 27 bits *)
          multN t1 z3 121665%N;   (* no prop *)        (* 44 bits *)
          addAssign t1 z2;        propagate t1;        (* 45 -> std *)
          mult z2 t1 z3;          propagateTwice z2;   (* std sized *)
          mult z3 x3 xB;          propagateTwice z3;   (* std sized *)
          square x3 t0;           propagate  x3        (* 40 sized *)
        ]%list.


    (** The result of the montgomery operation is to get a projective
       coordinates in x2 and z2. We need to convert this to affine
       coordinate followed by getting into the normalised form.

     *)

    Definition affinize : Repeat (statement progvar) :=
      List.concat [ propagate x2 : Repeat (statement progvar);           (* get x2 to std form from 41 bits *)
                    field.inverse x2 z2 t0  (* x₂ := x₂ z₂⁻¹  and in stdform   *)
        ].
    (** Montgomery step with a 64-bit scalar. Each step has to be done
        from high bits to low bits and hence the reverse iteration. We
        have also optimised on swap using the xor trick. This requires
        a final conditional swap at the end of all the steps.
     *)

    Variable smask : progvar of type Word64.
    Variable scalarWord  : progvar of type Word64.

    Definition doSwap    : code progvar := (field.swapE smask x2 x3 ++ field.swapE smask z2 z3)%list.
    Program Definition montgomeryWord i (_ : i < 4) : Repeat (statement progvar) :=
      let initSword := [code| scalarWord := scalar[i] |] in
      let updateSword := [code| scalarWord <<= `1` |] in
      let updateMask := let bit  := [verse| scalarWord >> `63` |] in
                        [code| smask ^= `field.mask bit` |] in
      let step := List.concat [updateMask ; doSwap; Step; updateSword ] in
      [Repeat.repeat 64 step].

    Definition sMaskInit : Repeat (statement progvar)  := [code| smask := `0` |].
    Program Definition montgomery : Repeat (statement progvar) :=
      ( sMaskInit
          ++ iterate_reverse montgomeryWord
          ++ (doSwap : Repeat (statement progvar))
      )%list.

    Definition x25519_code : Repeat (statement progvar) :=
      List.concat [  initialize : Repeat (statement progvar);
                     montgomery;
                     affinize;
                     field.reduce x2 B255 : Repeat (statement progvar)
        ]%list.
    End Locals.
    Definition x25519 := do x25519_code end.
  End Params.
End Internal.



Inductive name :=
| verse_curve25519_c_portable_clamp
| verse_x25519_c_portable.

Require Import Verse.Target.C.
Require Import Verse.Error.


Definition clamp  : CodeGen.Config.programLine + {Error.TranslationError}.
  Iterator verse_curve25519_c_portable_clamp
           Scalar
           Internal.ClampIter.
Defined.

Definition x25519 :  CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_x25519_c_portable (Internal.x25519).
Defined.

Definition clampI       : Compile.programLine := recover clamp.
Definition x25519C       : Compile.programLine := recover x25519.


Require Import Verse.Print.
(*
Goal to_print x25519C.
  print.
Abort.
*)

Definition program := verseC [ clampI ; x25519C].


Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name} (name : Name)
  := mkProgram name [ iterator verse_curve25519_c_portable_clamp
                               Scalar
                               Internal.ClampIter
                    ].
