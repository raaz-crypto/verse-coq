(** printing wi $w_i$ #w<sub>i</sub>#  *)
(** printing wi16 $w_{i+16}$ #w<sub>i+16</sub>#  *)
(** printing wi14 $w_{i+14}$ #w<sub>i+14</sub>#  *)
(** printing wi9 $w_{i+9}$ #w<sub>i+9</sub>#  *)
(** printing wi1 $w_{i+1}$ #w<sub>i+1</sub>#  *)

(** * The Verse EDSL.

Implementing cryptographic primitives in a High level language is
problematic for two reasons.

- The resulting code is not fast (enough), but more importantly

- The safety of the resulting program can be compromised due to side
  channel leaks.

Due to this unfortunate situation, cryptographic libraries, even for a
high level language like Haskell, has in it a lots of hand written C
and assembly code fragment. This is not a nice situation to be in.  As
a solution to this problem, we propose Verse, an embedded domain
specific language designed for writing cryptographic primitives. This
module serves as a short tutorial for Verse.


 *)

(** ** Getting started.

You will need coq (currently tested with 8.6 and 8.7) and the coq
library CoLoR.  We recommend the use of emacs and the proof general
mode for editing. The suggested means of developing verse code is
using opam however the CoLoR library has a bit of difficulty working
with sandboxing available with opam-2. When using opam-2 initialise
the repository using the command.

<< opam init -y --disable-sandboxing --compiler "$OCAML_VER" >>


 *)

(** ** A quick tour.


Cryptographic primitives come in two variety: bulk primitives and
fixed input ones. Primitives like ciphers, cryptographic hash
functions etc takes input as a stream of fixed sized chunks (called
blocks) and processes it and are examples for the former.  On the
other hand, the operations needed for asymmetric key primitives like
point multiplication in an elliptic curve are examples for the
latter. Being designed specifically for crypto-primitives, verse only
supports two kinds of functions.

- An iterator which can be thought of as a particular transformation,
  applied individually on each block of data in a stream of blocks, or

- Straight line programs which are a sequence of assembly language
  statements.

In particular, there are no facilities for performing any kind of
control flow except the implicit ones when the iterator loops over the
blocks. Not only are these two forms general enough to write
cryptographic primitives, restricting to such functions means that we
would not inadvertently use a secret information to execute a branch
thereby leaking information about secrets through the branch
predication.


Programming in Verse is carried out in two stages. In the first stage,
the Verse programmer writes a generic program which can potentially be
targeted at multiple architectures and in the second stage code
generation is done for specific targets. For the latter part the
programmer needs to tell the code generator which of the variables are
the parameters of the resulting C/assembly function, which of them are
to be spilled on stack and which are to be allocated in explicitly
given register list. While many of the mundane details are taken care
of by verse, there are two important considerations that the user
should worry about.

- In the first stage when writing generic code, care should be taken
  to avoid instructions that may not be available on the eventual
  target architecture. For example, if the target architecture is X86,
  a program that uses the instruction [X ::= Y [+] Z] will fail during
  code generation because of the lack of support for this 3-operand
  instruction in X86.

- During actual code generation verse takes care of using the
  appropriate calling convention for parameter passing and offset
  calculation on stack. However the register allocation is left to the
  user. The user should take care to avoid special registers that are
  reserved by the calling convention for otherwise code generation
  phase would fail.

We start by importing the verse module and setting up notations for
lists and vectors.

 *)

Require Import Verse.


(** *** Straight line functions

Let us give an example of a message scheduling for a sha2 like hash,
deliberately simplified to illustrate some of the constructs of the
language. The message is an array of 16x64-bit unsigned integers that
is expanded using the rule [wi16 = wi + wi14 + wi9 + wi1]. We will
wrap this code inside a module to preserve namespaces.

*)

Module SHA2.


  (** The standard idiom for writing a Verse program is to define a
      Coq [Section] which contains definitions of the program
      variables, Verse code, and other auxiliary information.
   *)

  Section SCHEDULE.

    (** The message schedule of SHA512 and SHA256 involves the same
        message indices. In our simplified variant, the only
        difference between the two is that the former uses words of
        64-bit whereas the latter uses words of 32-bit. By making the
        [word] a [Variable] of this section, our code effectively
        becomes polymorphic on the [word] type.  *)

    Variable word : type direct.

    (** The [type direct] in the above definition is the type of all
        direct types, i.e. types that fit into machine registers, which
        includes the word and multi-word types. See
        Section%~\ref{sec-type-system}% for more details on types
        and kinds in Verse.

     *)
    (** A SHA2 block is a 16 length array of this word type encoded
       in big endian.

     *)
    Definition SIZE  := 16.
    Definition BLOCK := Array SIZE bigE word.

    (**

       Generic variants of code are _parameterised_ over the program
       variables which will eventually be instantiated from the
       architecture specific register set during code generation. In
       Verse the type [VariableT] is the universe of all possible program
       variable types.

     *)

    Variable progvar     : VariableT.
    (* begin hide *)
    Arguments progvar [k] _.
    (* end hide *)

      (** What follows is the Verse program for message scheduling. First we
          "declare" the program variables, the variable [W], [S], and [T] followed
          by the actual message schedule.
       *)

    Variable W       : progvar BLOCK.
    Variable S T     : progvar word.

    (**

        We can index the [i]-th elements of the array [W] by using the
        notation [W[i]].  However, for safety verse does not allow
        such indexing without an accompanying proof of the fact that
        [i] is less than the bound. Instead of using the notation
        directly, we instead use a tactic also called `verse` whos
        joub is to complete such bounds. In the Definition below
        notice its use.

     *)
    Definition WordSchedule i  (boundPf : i < SIZE) :  code progvar.
      verse [ S  ::=  W[- i -];
              T  ::=  W[- (i + 14) mod SIZE -];
              S  ::=+ T;
              T  ::=  W[- (i + 9) mod SIZE  -];
              S  ::=+ T;
              T  ::= W[- (i + 1) mod SIZE -];
              S  ::=+ T;
              MOVE S TO W[- i -]
            ].
    Defined.


    (** Having defined the code segment for scheduling a single word
        in the message, we use the [foreach] function to generate an
        unrolled loop performing the [WordSchedule] for every index of
        [W].
     *)

    Definition Schedule := iterate WordSchedule.

    (** This completes the Verse code for word scheduling. An an
        exercise try removing the [mod SIZE] portion in the
        [WordSchedule] and look at the error message thrown out.

     *)

    (** ** Parameters, stack and register variables

       Notice that we have started the section by parameterising of
       over the program variables [progvar] and the variables [W],
       [S], and [T] of type [progvar t] for some appropriate type
       [t]. In the case of message scheduling, we would want [W] to be
       the parameter of the generated C function and [S] and [T] to be
       register variables in the architecture. We need some additional
       definitions (of type [Declaration]) here which will be used at
       the time of code generation.  *)


    Definition parameters : Declaration := [Var W].
    Definition stack      : Declaration := [].
    Definition registers  : Declaration := [Var S ; Var T].


    (** There is indeed some adhocness here arising out of the use of
        Coq sections.  Code generators expect the parameters to be
        listed first, followed by the stack variables, and finally the
        register variables. The order within the lists needs to be
        consistent with the listing in the section as well. Having
        made these extra declarations we are done with this section
        and we move on to code generation.
     *)

  End SCHEDULE.

End SHA2.


(** ** Legal

Copyright 2018, Piyush P Kurur

Licensed under the Apache License, Version 2.0 (the "License"); you
may not use this software except in compliance with the License.  You
may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied.  See the License for the specific language governing
permissions and limitations under the License.

SPDX-License-Identifier: Apache-2.0


 *)
