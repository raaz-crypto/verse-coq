Require Export CoLoR.Util.Vector.VecUtil.

Export VectorNotations.

Notation "h :: t" := (Vector.cons h t) (at level 60, right associativity) : vector_scope.

Open Scope vector_scope.
Delimit Scope vector_scope with vector.
