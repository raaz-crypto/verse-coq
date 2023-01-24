Require Import Verse.
Require Import BinNat.
Require Import Verse.CryptoLib.curve25519.c.field.
Import List.ListNotations.
(** * Curve 25519 and its parameters *)



Definition Word      := Word64.
Definition Element   := (Array 4 littleE Word).
Definition Scalar    := (Array 4 littleE Word).

Module Internal.

  Section Curve25519.
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
  End Curve25519.


  Section Montgomery.

    Context {progvar : VariableT}.

    Definition propagateTwice (x : feVar progvar) : code progvar := (propagate x ++ propagate x)%list.

    (* Base point *)
    Variable xB : feVar progvar.

    (* Point P *)
    Variable x2 z2 : feVar progvar.

    Variable x3 z3 : feVar progvar.

    Variable t0 t1 t2 t3 : feVar progvar.

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


TODO: Insert appropriate carry propagation.

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
        ].



    (** Montgomery step with a 64-bit scalar. Each step has to be done
        from high bits to low bits and hence the reverse iteration
     *)

    Definition doSwap (smask : progvar of type Word64) : code progvar := (field.swapE smask x2 x3 ++ field.swapE smask z2 z3)%list.
    Program Definition montgomeryWord (smask : progvar of type Word64) (w : expr progvar of type Word64) :=
      let ithBit i     := [verse| (w >> i) & `1` |] in
      let updateMask i := [code| smask ^= `field.mask (ithBit i)` |] in
      iterate_reverse (fun i (_ : i < 64) => updateMask i ++ doSwap smask ++ Step)%list.

    (* TODO: The toExpr is a eye sore fix it *)
    Program Definition montgomery
      (scalar : progvar of type Scalar)
      (smask  : progvar of type Word) :=
      ( let wexp (i : nat) (pf : i < 4) := toExpr [verse| scalar[i] |] : expr progvar of type Word in
        [code| smask := `0` |] ++
          iterate_reverse (fun i (pf : i < 4) => montgomeryWord smask (wexp i pf) )
                                                ++ doSwap smask
      )%list.
  End Montgomery.

End Internal.



Inductive name := verse_curve25519_c_portable_clamp.

Require Import Verse.Target.C.
Require Import Verse.Error.


Definition clamp  : CodeGen.Config.programLine + {Error.TranslationError}.
  Iterator verse_curve25519_c_portable_clamp
           Scalar
           Internal.ClampIter.
Defined.

Definition clampI       : Compile.programLine := recover clamp.

Definition program := verseC [ clampI ].


Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name} (name : Name)
  := mkProgram name [ iterator verse_curve25519_c_portable_clamp
                               Scalar
                               Internal.ClampIter
                    ].
