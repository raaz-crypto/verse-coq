(* * The Verse EDSL.

Implementing cryptographic primitives in a High level language is
problematic for two reasons.

1. The resulting code is not fast (enough), but more importantly

2. The safety of the resulting program can be compromised due to side
   channel leaks.

Due to this unfortunate situation, cryptographic libraries, even for a
high level language like Haskell, has in it a lots of hand written C
and assembly code fragment. This is not a nice situation to be in.

As a solution to this problem, we propose Verse, an embedded domain
specific language specifically designed for writing cryptographic
primitives. This module serves as a short tutorial for using Verse.

*)

(* ** Getting started.

Our aim is to make Verse's surface syntax clean enough so that

1. Cryptographic implementations written in Verse should be readable
   even to a user who does not know Coq. Cryptographic libraries
   require a great deal of expert review. It should be possible for a
   cryptographic experts who might not know much of Coq to follow the
   intricacies of the code. To this end, we have made the surface
   syntax of Verse mimic the syntax of a typical imperative language
   with symbolic variables, assignment statements and array indexing.

2. Cryptographic implementations should be writable by a programmer
   with a working knowledge of Coq, without worrying about the
   internals of Coq. The verse language is designed to be correct by
   construction which throws up a lot of proof obligations. We have
   automatic tactics to dispose these of.


Therefore, we believe that you can get started with verse with almost
no knowledge of coq or verse. If you want to hack on verse code, you
will need coq (currently tested with 8.6 and 8.7) and the coq library
CoLoR.  The suggested means of developing verse code is using
opam. However, the CoLoR library has issues with the opam-2. So we
recommend using opam-1.2.2. We also recommend the use of emacs and the
proof general mode for editing.

*)

(* ** A quick tour.

Verse is really a low level language with an instruction set that can
be directly translated (almost 1:1) to the instruction set of a
typical general purpose machine architecture like x86. So one can
really program pretty close to the machine including controlling
aspects like register allocation. This is very important because we
would like to exactly predict the emitted code so that we can control
side channel leakages. However, verse exploits the fact that it is
embedded in Coq to give the programmer a markedly high level
experience.

* Verse is equipped with a type system that is rich enough to even
  prevent errors in array indexing and endian conversion.

* One can generate Verse code using functions written in Gallina which
  behave like macros for code generation

* Many of the type safety property in verse is achieved by making the
  verse language correct by construction. However, this does not
  become proof burden to the user thanks to Ltac.

* Finally, the interactive mode like proof general, gives an IDE like
  experience when building complicated programs.

 *)


(* ** Legal

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
