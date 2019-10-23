

(* begin hide *)
Definition to_print {A}(a : A) := False.
Global Opaque to_print.

Ltac print := cbv; match goal with
                   | [ |- _ ?G ] => idtac G
                   end; trivial.

(* end hide *)

(**

This module uses the idtac to print pretty printed code. The following
idiom can be use to print stuff, in our case pretty printed programs.
Thanks to /u/Syrak on reddit for this cool trick.

<<

Goal to_print 2.
  print.
Abort.

>>

*)
