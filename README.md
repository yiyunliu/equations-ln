An interactive tutorial on specifying and implementing the simply-typed
lambda calculus in Coq using a locally nameless representation.

This version uses the [Equations](https://github.com/mattam82/Coq-Equations)
Coq package to index the expression type with the number of bound
variables. This definition means that the local closure predicate is not
needed --- instead the type "exp 0" only contains locally closed terms.


INSTALLATION

  This tutorial depends on the `Metalib.Metatheory` library, available from
  [https://github.com/plclub/metalib](https://github.com/plclub/metalib).
  Make sure that you compile and install this library _first_.

  You also need to install the equations library.

  After you have done that, you can use make

    `make`             - Compile all Coq files

CONTENTS

     _CoqProject       - list of modules

     Classes.v         - type class definitions for operations on 
                         syntax (open/close/etc) and their properties

     Fin.v             - Finite numbers, defined using equations
     
     Definitions.v     - Specification of STLC using locally nameless
                         representation (LN)
                         
     Lemmas.v          - infrastructure lemmas about binding, similar 
                         to the form generated by LNgen
                         
     Lec2.v            - type soundness for STLC


QUESTIONS


- Should we use ssreflect? especially for reasoning about equality of atoms in metalib?

- Why does lia not work in some of the proofs in Lemmas.v
