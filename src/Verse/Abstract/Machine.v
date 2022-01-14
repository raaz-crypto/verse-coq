(* begin hide *)
Require Import Verse.Monoid.
Require Import Verse.Utils.hlist.
Require List.
Import List.ListNotations.

Declare Custom Entry machine.
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

    Definition puts_list (s : slice fam fam') (mem : memory fam') := toList (puts_hlist s mem).
    Definition puts (s : slice fam fam') (mem : memory fam') (start : memory fam) : memory fam
      := hlist.foldl (fun _ (m : memory fam)  (tr : memory fam -> memory fam) => tr m) start (puts_hlist s mem).

    Definition puts_from_right (s : slice fam fam') (mem : memory fam') (start : memory fam) : memory fam
      := hlist.foldr (fun _  (tr : memory fam -> memory fam) (m : memory fam)  => tr m) start (puts_hlist s mem).

  End SliceOperations.

  (** ** Linear slice.

   This is an alternative to distinctness of variables as far as I see
   it.

   *)

  Definition linear {fam fam'} (s : slice fam fam') := forall (start : memory fam) (mem : memory fam'),
      gets s (puts s mem start)  = mem.

  Definition function  (inp : family) (tau : type) := hlist.curried A (A tau) inp.
  Definition updateWith {tau : type}{fam inp : family}(adr : address fam tau) (f : function inp tau)(args : slice fam inp)
    : memory fam -> memory fam :=
    fun mem => put adr (uncurry f (gets args mem)) mem.


  Record subroutine (inp out : family) :=
    { requirement : memory inp -> Prop;
      transform   : memory inp -> memory out;
      guarantee   : memory inp -> memory out -> Prop;
    }.

  Arguments requirement {inp out}.
  Arguments transform   {inp out}.
  Arguments guarantee   {inp out}.

  Definition VC {inp out}(sr : subroutine inp out) : Prop := forall i : memory inp, requirement sr i -> guarantee sr i (transform sr i).
  Definition vsubroutine (inp outp : family) := { sr : subroutine inp outp | VC sr }.

End Machine.


Notation "[machine| e |]" := e (e custom machine).
Notation "x" := x     (in custom machine at level 0, x global).
Notation "( x )" := x  (in custom machine at level 0).
Notation "` x `" := x  (in custom machine at level 0, x constr).
Notation "idx := v " := (fun mem => put idx v) (in custom machine at level 61).
Notation "idx := F ( A , .. , B )" := (updateWith _ idx F (hcons A .. (hcons B hnil) ..)) (in custom machine at level 61).
Notation "[mcode| X ; .. ; Y |]" := (cons X .. (cons Y nil) ..) (X custom machine, Y custom machine).


Module Examples.

Definition mymem := hlist (fun x => x) [nat ; nat ; bool ].

Definition myfunction l := function (fun x => x) l.
Definition succ : myfunction [nat]%list nat := S.
Definition negate : myfunction [bool]%list bool := negb.
Definition x  : nat ∈ [nat ; nat ; bool] := hfirst.
Definition y  : nat ∈ [nat ; nat ; bool] := hnext hfirst.
Definition z  : bool ∈ [nat ; nat ; bool] := hnext (hnext hfirst).
Definition equals : myfunction [nat ; nat]%list bool := Nat.eqb.
Definition upD : list (mymem -> mymem) := [mcode|
                                          `x` := `succ` ( `x` ) ;
                                          `z` := `equals` ( `x` , `y` )
                                         |].

End Examples.
