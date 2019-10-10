Require Import Verse.Target.C.Ast.
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
Notation "'0x0'" := Ox0 (only printing): c_scope.
Notation "'0x1'" := Ox1 (only printing): c_scope.
Notation "'0x2'" := Ox2 (only printing): c_scope.
Notation "'0x3'" := Ox3 (only printing): c_scope.
Notation "'0x4'" := Ox4 (only printing): c_scope.
Notation "'0x5'" := Ox5 (only printing): c_scope.
Notation "'0x6'" := Ox6 (only printing): c_scope.
Notation "'0x7'" := Ox7 (only printing): c_scope.
Notation "'0x8'" := Ox8 (only printing): c_scope.
Notation "'0x9'" := Ox9 (only printing): c_scope.
Notation "'0xA'" := OxA (only printing): c_scope.
Notation "'0xB'" := OxB (only printing): c_scope.
Notation "'0xC'" := OxC (only printing): c_scope.
Notation "'0xD'" := OxD (only printing): c_scope.
Notation "'0xE'" := OxE (only printing): c_scope.
Notation "'0xF'" := OxF (only printing): c_scope.


Require Vector.
Require Import Verse.Language.Types.
Import Vector.VectorNotations.

Notation "/**/~ X"  := (app bitComp [ X ])
                         (at level 30, right associativity, only printing) : c_scope.
Notation "X [ I ]"  := (index X I)
                         (at level 29, only printing)    : c_scope.

Infix "*"           := (app mul)
                         (at level 40, left associativity, only printing) : c_scope.
Infix "/"           := (app quot)
                         (at level 40, left associativity, only printing) : c_scope.
Infix "%"           := (app rem)
                         (at level 40, left associativity, only printing) : c_scope.

Infix "+"           := (app plus)
                         (at level 50, left associativity, only printing) : c_scope.
Infix "-"           := (app minus)
                         (at level 50, left associativity, only printing) : c_scope.

Notation "X  <<  N" := (app (shiftL N) [ X ])
                         (at level 55, left associativity, only printing) : c_scope.
Notation "X  >>  N" := (app (shiftR N) [ X ])
                         (at level 55, left associativity, only printing) : c_scope.

Infix "&"           := (app bitAnd)
                         (at level 56, left associativity, only printing) : c_scope.
Infix "/**/^/**/"   := (app bitXor)
                         (at level 57, left associativity, only printing) : c_scope.
Infix "|"           := (app bitOr)
                         (at level 58, left associativity, only printing) : c_scope.


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

Notation "'verse_to_be32' ( X )" := (convert_to bigE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_to_be64' ( X )" := (convert_to bigE uint64_t X)
         (at level 0, only printing) : c_scope.


Notation "'verse_to_le16' ( X )" := (convert_to littleE uint16_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_to_le32' ( X )" := (convert_to littleE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_to_le64' ( X )" := (convert_to littleE uint64_t X)
         (at level 0, only printing) : c_scope.


Notation "'verse_from_be16' ( X )" := (convert_from bigE uint16_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_be32' ( X )" := (convert_from bigE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_be64' ( X )" := (convert_from bigE uint64_t X)
         (at level 0, only printing) : c_scope.


Notation "'verse_from_le16' ( X )" := (convert_from littleE uint16_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_le32' ( X )" := (convert_from littleE uint32_t X)
         (at level 0, only printing) : c_scope.

Notation "'verse_from_le64' ( X )" := (convert_from littleE uint64_t X)
         (at level 0, only printing) : c_scope.

Definition binOpUpdate (o : op 2) X Y := C.Ast.update 1 o X [ Y ].
Definition uniOpUpdate (o : op 1) X   := C.Ast.update 0 o X [].

Infix "="     := (assign)             (at level 70, only printing) : c_scope.
Infix "+="    := (binOpUpdate plus)   (at level 70, only printing) : c_scope.
Infix "-="    := (binOpUpdate minus)  (at level 70, only printing) : c_scope.
Infix "*="    := (binOpUpdate mul)    (at level 70, only printing) : c_scope.
Infix "/="    := (binOpUpdate quot  ) (at level 70, only printing) : c_scope.
Infix "%="    := (binOpUpdate rem   ) (at level 70, only printing) : c_scope.
Infix "|="    := (binOpUpdate bitOr ) (at level 70, only printing) : c_scope.
Infix "&="    := (binOpUpdate bitAnd) (at level 70, only printing) : c_scope.
Infix "^="    := (binOpUpdate bitXor) (at level 70, only printing) : c_scope.

Notation "X <<= N" := (uniOpUpdate (shiftL N) X) (at level 70, only printing) : c_scope.
Notation "X >>= N" := (uniOpUpdate (shiftR N) X) (at level 70, only printing) : c_scope.
Notation "++ X"    := (increment X)   (at level 70, only printing) : c_scope.
Notation "-- X"    := (decrement X)   (at level 70, only printing) : c_scope.


Notation "/* 'End' 'Block' */" :=
         (endBlock) (at level 70, only printing) : c_scope.
Notation "X ; Y"
  := (sequence X Y) ( at level 71, only printing, format "X ; '//' Y" ) : c_scope.

Notation "'while' ( X > 0 ) { Y }" := (while X Y)
         ( at level 70, only printing,
           format "'while' ( X > 0 ) '//' { Y }"
         ) : c_scope.


Notation "/*No Loop*/" := None (at level 0, only printing).
Notation "'/* 'Iterate' 'over' 'blocks' */' B" := (Some B) (at level 0, only printing)  : c_scope.
Notation "'auto' X" := (declareStmt X) (at level 70, only printing) : c_scope.


Notation "'void' FN PS { S W F }" := (void_function FN PS S W F)
         ( at level 70, only printing,
           format "'void'  FN PS '//' { '[v    ' '//' S '//' W '//' F ']' '//' }"
         ) : c_scope.

Delimit Scope c_scope with clang.
