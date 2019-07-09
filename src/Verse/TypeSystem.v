(**

A generic types system for verse and its target languages. There are
two kinds of types the direct type and the memory type. Direct types
are types whose values can reside directly in program variables (or
registers in the case of machines). Memory types are those whose that
are accessed through indirect referencing.


 *)
Inductive kind : Type := direct | memory.

Structure typeSystem :=
  TypeSystem { type   : kind -> Type;
               const  : type direct -> Type;
             }.
