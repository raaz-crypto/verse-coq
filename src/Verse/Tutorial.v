(** printing wi %w_i% #w<sub>i</sub>#  *)
(** printing wi16 %w_{i+16}% #w<sub>i+16</sub>#  *)
(** printing wi14 %w_{i+14}% #w<sub>i+14</sub>#  *)
(** printing wi9 %w_{i+9}% #w<sub>i+9</sub>#  *)
(** printing wi1 %w_{i+1}% #w<sub>i+1</sub>#  *)

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

We believe that one can get started with verse with minimal knowledge
of coq or verse. If you want to hack on verse code, you will need coq
(currently tested with 8.6 and 8.7) and the coq library CoLoR.  The
suggested means of developing verse code is using opam. However, the
CoLoR library has issues with the opam-2. So we recommend using
opam-1.2.2. We also recommend the use of emacs and the proof general
mode for editing.

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



 *)

(** *** Straight line functions

Let us give an example of a message scheduling for a sha2 like hash,
deliberately simplified to illustrate some of the constructs of the
language. The message is an array of 16x64-bit unsigned integers that
is expanded using the rule [wi16 = wi + wi14 + wi9 + wi1].


*)

(*

Verse is really a low level language with an instruction set that can
be directly translated almost 1:1 to the instruction set of a typical
general purpose machine architecture like x86. This enables one to
write programs that are pretty close to the machine including
controlling aspects like register allocation. Such a low level
interface is a necessary so that we can exactly predict the emitted
code and control side channel leakages. Yet verse is a typed language
with a type system rich enough to even prevent errors in array
indexing and endian conversion. One should therefore think of verse as
a typed assembly language like LLVM (but with types that are in some
aspects more powerful).

Despite the above restrictions, we would like the programming
experience to be high level. We will exploit the embedded nature of
verse to our advantage.

- Verse programs are represented as inductive types in Gallina hand
  hence we can write code generations and manipulation functions in
  Gallina which can act like macros. The Verse system comes with some
  standard such macros that implement things like loops etc.

- The type safety property in verse is achieved by making the verse
  language correct by construction. However, this does not become
  proof burden to the programmer due to tatics that we have exported
  from Verse.

- Using the "Notation" feature of coq, the surface syntax of Verse
  mimic the syntax of a typical imperative language with symbolic
  variables, assignment statements and array indexing. This enhances
  the readability and writeability of verse programs.

- Finally, the interactive mode like proof general, gives an IDE like
  experience when building complicated programs.




 *)


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
