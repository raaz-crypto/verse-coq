(* begin hide *)
Require Import Verse.Monoid.
Require Import Verse.Utils.hlist.
Require List.
Import List.ListNotations.

(* end hide *)

Set Universe Polymorphism.
(** * An (family of) abstract machine.

To given semantics to straight line program, we define an abstract
(typed) machine inside Coq with programs being "compiled into" this
machine. These are finite memory machines where the entire memory is
divided into finitely many cells. Each cell is associated where type
[τ : Type].

We have a machine for each element in the type [family] which is
nothing but a list of types that the cells of the machine have. The
(contents of the) memory of such a machine is represented by an hlist
and the indices into this hlist, serves as memory cells.

 *)

Definition family := list Type.
Definition memory (fam : family) := hlist (fun tau => tau) fam.
Definition cell   (fam : family)(tau : Type) :=  tau ∈ fam.


(** Two very basic operations on the memory is the get and put functions which we define now *)

Section BasicOperations.
  Context {fam : family}{tau : Type}.
  Definition get : cell fam tau -> memory fam -> tau
    := index.
  Definition put (c : cell fam tau) (x : tau) (mem : memory fam) : memory fam
    := update c mem x.
End BasicOperations.


(** ** Memory slices

We would want to generalize the get and put operations and in this
generalized setting we deal with memory slices. A slice is just an
ordered collection of cells of the original memory.

*)

Definition slice (fam : family) := hlist (cell fam).

(*

This is another way look at slices, it is a memory that contains
pointers to the other memory. Making it work requires universe
polymorphism definition in hlist and in this file.

 *)
Definition pointers (fam : family) := fun fam' => memory (List.map (fun tau => cell fam tau) fam').


Fixpoint full_slice (fam : family) : slice fam fam :=
  match fam with
  | []%list => []%hlist
  | (x :: xs)%list => let xsslice := full_slice xs in
                    (hfirst :: hlist.map (fun tau (e : tau ∈ xs) => hnext e)  xsslice)%hlist
  end.


(** We now define get and put like operation on memory slices *)
Section SliceOperations.
  Context {fam fam' : family}.

  (** Getting a slice gives the memory of appropriate type *)
  Definition gets (s : slice fam fam') (mem : memory fam) : memory fam'
    := hlist.map (fun tau c => get (tau:=tau) c mem) s.

  (* begin hide *)
  Definition puts_hlist (s : slice fam fam') (mem : memory fam') := hlist.zipWith (fun _ c v => put c v) s mem.
  (* end hide *)

  (** The puts operation gives a list of possible updates to the
      memory location. The overall effect on the memory depends on the
      order that these operations are executed. Of particular interest
      is two variants one which does the operations from left to right
      where as the other which does the operations from right to
      left *)

  Definition puts (s : slice fam fam') (mem : memory fam') := toList (puts_hlist s mem).
  Definition puts_from_left (s : slice fam fam') (mem : memory fam') (start : memory fam) : memory fam
    := hlist.foldl (fun _ (m : memory fam)  (tr : memory fam -> memory fam) => tr m) start (puts_hlist s mem).

  Definition puts_from_right (s : slice fam fam') (mem : memory fam') (start : memory fam) : memory fam
    := hlist.foldr (fun _  (tr : memory fam -> memory fam) (m : memory fam)  => tr m) start (puts_hlist s mem).

End SliceOperations.

(** ** Linear slice.

This is an alternative to distinctness of variables as far as I see
it.

*)

Definition linear {fam fam'} (s : slice fam fam') := forall (start : memory fam) (mem : memory fam'),
    puts_from_left s mem start  = puts_from_right s mem start.
