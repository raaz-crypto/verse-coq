Require Import Arith.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.FFI.Raaz.


Definition counterType := Word 64.
Fixpoint translate {k} (ty : typeOf verse_type_system k) : Raaz.type
  := match ty with
     | word n
       => match n with
         | 0 | 1 | 2 | 3 => Word (2^n * 8)
         | _ => Tuple (2^(n-3)) (Word 64)
         end
     | multiword m n
       => match n with
         | 0 | 1 | 2 | 3 => Tuple (2^m) (Word (2^n * 8))
         | _             => let mp := m + n - 3 in
                           Tuple (2^mp) (Word 64)
         end
     | Types.array b e ty
       => match b with
         | 1 => setEndian e (Ptr (translate ty))
         | _ => setEndian e (Ptr (Tuple b (translate ty) ))
         end
     end.

Require Import Verse.
Definition fromDecl {n}(params : @Declaration n) : list Raaz.type
  := List.map (fun st => translate (projT2 st)) (Vector.to_list params).


Require Verse.
Require Verse.Scope.
(** Generate the Haskell FFI stub for a straight line function *)
Definition function {Name} (name : Name)
           {T}{ifr : Infer T} (params : T)
  : Raaz.line
  := let ps := Verse.infer params in ccall name (args (fromDecl ps)).

(** Generate the Haskell FFI stub for an iterator *)
Definition iterator
           {Name} (name : Name)
           (memty : typeOf verse_type_system memory)
           {T}{ifr : Infer T} (params : T)
  : Raaz.line :=
  let ps    := fromDecl (Verse.infer params) in
  let block := translate memty in
  ccall name (args (block :: counterType :: ps))%list.
