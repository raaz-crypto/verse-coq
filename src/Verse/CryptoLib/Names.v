Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.

Record Name := { primitive : string;
                 arch : string;
                 features : list string
              }.

Fixpoint concatSep (sep : string)(l : list string) : string :=
  match l with
  | [ ]       => ""
  | [x]       => x
  | (x :: xs) => x ++ sep ++ concatSep sep xs
  end.

Definition details (n : Name) := concatSep "_" (features n).

Definition cFunName (n : Name) : string :=
  concatSep "_" (["verse"%string ; primitive n; arch n] ++ features n)%list.

Definition libVerseFilePath (n : Name) : string :=
  concatSep "/" ["libverse"%string; primitive n; arch n; details n].
