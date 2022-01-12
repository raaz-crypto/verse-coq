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
divided into finitely many cells.

We have a machine for each element in the type [family] which is
nothing but a list of types that the cells of the machine have. The
(contents of the) memory of such a machine is represented by an hlist
and the indices into this hlist, serves as memory cells.

 *)

Section Machine.

  Context {type : Type} (** The types of the machine *)
          (A : type -> Type).

  (** We have a family of machines one for each possible list of types. The list of
      types give the types of the memory cells of the machine (in that order)
   *)
  Definition family := list type.

  (** The memory of the machine is just the appropriate hlist *)
  Definition memory  (fam : family) := hlist A fam.
  Definition address (fam : family)(tau : type) :=  tau ∈ fam.


  Definition get {fam : family}{tau : type} : address fam tau -> memory fam -> A tau
    := index.
  Definition put {fam : family}{tau : type} (addrs : address fam tau) (x : A tau) (mem : memory fam) : memory fam
    := update addrs mem x.

  (** ** Memory slices

   We would want to generalize the get and put operations and in this
   generalized setting we deal with memory slices. A slice is just an
   ordered collection of cells of the original memory.

   *)

  Definition slice (fam : family) := hlist (address fam).


  (** We now define get and put like operation on memory slices *)
  Section SliceOperations.
    Context {fam fam' : family}.

    (** Getting a slice gives the memory of appropriate type *)
    Definition gets (s : slice fam fam') (mem : memory fam) : memory fam'
      := hlist.map (fun tau c => get (tau:=tau) c mem) s.

    (* begin hide *)
    Definition puts_hlist (s : slice fam fam') (mem : memory fam')
      := hlist.zipWith (fun _ c v => put c v) s mem.
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

  (** NOTE: I now have second thoughts about the above definition of
      linearity. Maybe something based on distinctness is probably
      what is more relevant.
   *)


  (** TODO: needs some cleanup *)

  Record procedure (global : family) :=
    {
    inp : family;
    inpSlice : slice global inp;
    out : family;
    outSlice : slice global out;  (* this needs to be linear for things to fit in *)

    requirement : memory inp -> Prop;
    (* The procedure can be called only if the input satisfies this property *)
    transform    : memory inp -> memory out;

    guarantee : memory out -> Prop;

    verification_condition : forall i : memory inp, requirement i -> guarantee (transform i) }.

  Definition program (fam : family) :=  list (procedure fam).
  Print True.
  Definition apply {fam}(proc : memory fam -> memory fam) : procedure fam :=
    {|
    inp      := fam;
    inpSlice := all_membership fam;
    out      := fam;
    outSlice := all_membership fam;
    requirement := (fun _ => True);
    transform := proc;
    guarantee := (fun _ => True);
    verification_condition := fun _ _ => I
    |}.

End Machine.
