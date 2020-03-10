Require Import Verse.Target.C.Ast.
Require Import Verse.TypeSystem.
Import Verse.Target.C.Ast.Expr.

Notation "T X"
  := (declare_variable T X)
       (at level 29, only printing) : c_scope.

Notation "T X [ N ]"
  := (declare_variable (array N T) X)
       (at level 29, only printing,
        format "T  X [ N ]"
       ) : c_scope.

Notation "T (* X ) [ N ]"
  := (declare_variable (ptrToArray N T) X)
       (at level 29, only printing,
        format "T  '(*' X ')' [ N ]"
       ) : c_scope.

(** * Pretty printing constants *)
Require Import Verse.Nibble.

Notation "'0'" := Ox0 (only printing) : c_scope.
Notation "'1'" := Ox1 (only printing) : c_scope.
Notation "'2'" := Ox2 (only printing) : c_scope.
Notation "'3'" := Ox3 (only printing) : c_scope.
Notation "'4'" := Ox4 (only printing) : c_scope.
Notation "'5'" := Ox5 (only printing) : c_scope.
Notation "'6'" := Ox6 (only printing) : c_scope.
Notation "'7'" := Ox7 (only printing) : c_scope.
Notation "'8'" := Ox8 (only printing) : c_scope.
Notation "'9'" := Ox9 (only printing) : c_scope.
Notation "'a'" := OxA (only printing) : c_scope.
Notation "'b'" := OxB (only printing) : c_scope.
Notation "'c'" := OxC (only printing) : c_scope.
Notation "'d'" := OxD (only printing) : c_scope.
Notation "'e'" := OxE (only printing) : c_scope.
Notation "'f'" := OxF (only printing) : c_scope.

Require Vector.
Require Import Verse.Language.Types.
Import Vector.VectorNotations.
Notation "/**/~ X"  := (app bitComp [ X ])
                         (at level 30, right associativity, only printing) : c_scope.
Notation "* X"      := (ptrDeref X) (at level 29,
                                     format "* X",
                                     only printing) : c_scope.
Notation "X [ I ]"  := (index X I)
                         (at level 29,
                          format "X [ I ]",
                          only printing)    : c_scope.

Notation "X * Y "   := (app mul [ X ; Y ])
                         (at level 40, left associativity, only printing) : c_scope.
Notation "X / Y"    := (app quot [ X ; Y])
                         (at level 40, left associativity, only printing) : c_scope.
Notation "X % Y"       := (app rem  [ X ; Y])
                         (at level 40, left associativity, only printing) : c_scope.

Notation "X + Y"           := (app plus [X; Y])
                         (at level 50, left associativity, only printing) : c_scope.
Notation "X - Y"           := (app minus [ X; Y] )
                         (at level 50, left associativity, only printing) : c_scope.

Notation "X  <<  N" := (app (shiftL N) [ X ])
                         (at level 55, left associativity, only printing) : c_scope.
Notation "X  >>  N" := (app (shiftR N) [ X ])
                         (at level 55, left associativity, only printing) : c_scope.

Notation "X & Y" := (app bitAnd [X ; Y])
                      (at level 56, left associativity, only printing) : c_scope.

Notation "X 'XOR' Y"  := (app bitXor [X; Y])
                             (at level 57, left associativity, only printing) : c_scope.
Notation "X | Y"          := (app bitOr [X; Y])
                         (at level 58, left associativity, only printing) : c_scope.
Notation "'0x' X Y 'U'"
  := (verse_const uint8_t (cons X (cons Y nil) ))
       ( at level 0,
         format "'0x' X Y 'U'",
         only printing) : c_scope.

Notation "'0x' X .. Y 'U'"
  := (verse_const uint16_t (cons X .. (cons Y nil) ..))
       ( at level 0,
         format "'0x' X .. Y 'U'",
         only printing) : c_scope.

Notation "'0x' X .. Y 'UL'"
  := (verse_const uint32_t (cons X .. (cons Y nil) ..))
       ( at level 0,
         format "'0x' X .. Y 'UL'",
         only printing) : c_scope.

Notation "'0x' X .. Y 'ULL'"
  := (verse_const uint64_t (cons X .. (cons Y nil) ..))
       ( at level 0,
         format "'0x' X .. Y 'ULL'",
         only printing) : c_scope.

Notation "'verse_rotL8'"  := (rotateL uint8_t)  (at level 0, only printing) : c_scope.
Notation "'verse_rotL16'" := (rotateL uint16_t) (at level 0, only printing) : c_scope.
Notation "'verse_rotL32'" := (rotateL uint32_t) (at level 0, only printing) : c_scope.
Notation "'verse_rotL64'" := (rotateL uint64_t) (at level 0, only printing) : c_scope.

Notation "'verse_rotR8'"  := (rotateR uint8_t)  (at level 0, only printing) : c_scope.
Notation "'verse_rotR16'" := (rotateR uint16_t) (at level 0, only printing) : c_scope.
Notation "'verse_rotR32'" := (rotateR uint32_t) (at level 0, only printing) : c_scope.
Notation "'verse_rotR64'" := (rotateR uint64_t) (at level 0, only printing) : c_scope.

Notation "'verse_to_be16' ( X )" := (convert_to bigE uint16_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_to_be32' (  X  )" := (convert_to bigE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_to_be64' (  X  )" := (convert_to bigE uint64_t X)
         (at level 0, only printing) : c_scope.


Notation "'verse_to_le16' (  X  )" := (convert_to littleE uint16_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_to_le32' (  X  )" := (convert_to littleE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_to_le64' (  X  )" := (convert_to littleE uint64_t X)
         (at level 0, only printing) : c_scope.


Notation "'verse_from_be16' (  X  )" := (convert_from bigE uint16_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_be32' (  X  )" := (convert_from bigE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_be64' (  X  )" := (convert_from bigE uint64_t X)
         (at level 0, only printing) : c_scope.


Notation "'verse_from_le16' (  X  )" := (convert_from littleE uint16_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_le32' (  X  )" := (convert_from littleE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_le64' (  X  )" := (convert_from littleE uint64_t X)
         (at level 0, only printing) : c_scope.


Infix "="         := (assign)              (at level 70, only printing) : c_scope.
Notation "X += Y" := (update X plus [Y]) (at level 70, only printing) : c_scope.
Notation "X -= Y" := (update X minus  [Y]) (at level 70, only printing) : c_scope.
Notation "X *= Y" := (update X mul    [Y]) (at level 70, only printing) : c_scope.
Notation "X /= Y" := (update X quot   [Y]) (at level 70, only printing) : c_scope.
Notation "X %= Y" := (update X rem    [Y]) (at level 70, only printing) : c_scope.
Notation "X |= Y" := (update X bitOr  [Y]) (at level 70, only printing) : c_scope.
Notation "X &= Y" := (update X bitAnd [Y]) (at level 70, only printing) : c_scope.
Notation "X ^= Y" := (update X bitXor [Y]) (at level 70, only printing) : c_scope.

Notation "X <<= N" := (update X (shiftL N) []) (at level 70, only printing) : c_scope.
Notation "X >>= N" := (update X (shiftR N) []) (at level 70, only printing) : c_scope.
Notation "++ X"    := (increment X)   (at level 70, only printing) : c_scope.
Notation "-- X"    := (decrement X)   (at level 70, only printing) : c_scope.
Notation "X > 0" := (gt_zero X) (at level 70, only printing) : c_scope.

Notation "{;}" := (Braces nil) : c_scope.

Notation "{ X ; }"
  := (Braces (cons X nil))
       (at level 0, only printing, right associativity
        , format "{ '[  ' '//' X ; '//' ']' }") : c_scope.

Notation "{ X ; .. ; Y ; }"
  := (Braces (cons X .. (cons Y nil) .. ))
       (at level 0, only printing, right associativity
        , format "{ '[  ' '//' X ; '//' .. ; '//' Y ; ']' '//' }") : c_scope.

Notation "( X )"
  := (params (cons X nil))
       (only printing, format "( X )") : c_scope.
Notation "( 'void' )"
  := (params nil)
       (only printing, format "( 'void' )" ) : c_scope.
Notation "( X , .. , Y )"
  := (params (cons X .. (cons Y nil)..))
       (only printing) : c_scope.

Notation "# 'include' < FILE >"
  := (include FILE)
       (at level 8, only printing,
        format "#  'include'  < FILE > '//'").

Notation "'void' FN P BODY"
  := (function FN P BODY)
       (at level 8, only printing,
        format "'void'  FN  P '//' BODY") : c_scope.

Notation "'while' ( COND ) BODY"
  := (whileLoop COND BODY)
       (at level 70, only printing,
        format "'while'  ( COND ) '//' BODY") : c_scope.




Notation "'auto' X" := (declareStmt X) (at level 70, only printing) : c_scope.


Open Scope c_scope.

Import List.ListNotations.
