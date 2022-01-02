
# Table of Contents

1.  [Project Hata](#org7e2bcb5)
    1.  [Goal](#org8da3ac2)
    2.  [Philosophy](#org7130199)
    3.  [Current state](#org929413b)
        1.  [Concerning formalization of mathematics](#orga914e54)
        2.  [Concerning execution of the code](#org3cd892c)
        3.  [Concerning compilation to pdf](#orgdd84ff6)


<a id="org7e2bcb5"></a>

# Project Hata


<a id="org8da3ac2"></a>

## Goal

The goal of this project is to formalize enough mathematics (category theory, algebra) to
be able to do proper verified development of theoretical computer science, i.e., type theory,
logic, algorithms, compilation.

Currently, the focus is on creating a theory of type checking / type inference systems. It should
include the full pipeline a real world programming language needs to have: from a collection of files
in the file system via an interactive editor to an internal data type of well typed terms of that language.
This means that a proper way to record errors, as well as information derived during the inference process
will be a core part of the theory.


<a id="org7130199"></a>

## Philosophy

The philosophy of the formalization is that 3 aspects should be accommodated with as few
compromises as possible:

-   The code should compile into a native binary.
-   The code should also be compilable into a pdf file, producing a mathematical document akin to the ones
    written by hand.
-   Finally the source files itself should remain humanly readable, i.e. all commentary intended for the pdf should
    be formatted without much syntactic overhead. This means that a markdown-like language is more preferrable
    than e.g. Tex.


<a id="org929413b"></a>

## Current state

In the following the current state of different features is shown.
Explanation of the checkboxes:

-   [X] A checked box means that this topic is implemented.
    (with a certain amount of corresponding proofs which would usually be expected)
-   [ ] An unchecked box means that this topic is not implemented yet,
    but is considered for future implementation.
-   [ ] [REW/WIP] An unchecked box with an annotation means that this topic is currently in development (WIP), or that it
    once was implemented, but is currently pending a rewrite (REW) (being out of date because of rewrites in other places).


<a id="orga914e54"></a>

### Concerning formalization of mathematics

-   Infrastructural/Meta:
    -   [X] System for dealing with mathematical subtyping hierarchies (e.g. Group ⊑ Ring ⊑ Field)
    -   [X] Decrease syntactic overhead for universe levels
-   Algebra
    -   [X] Definition of Monoid, Group, Abelian, Ring, CRing
    -   [X] Definition of Ordered rings
    -   [X] Localization of CRings
    -   [ ] Specific
        -   [X] ℚ as localization of ℤ
        -   [X] ℝ as Dedekind completion of ℚ
-   Order theory
    -   [X] Definition of Preorder, Partialorder, Totalorder, Lattice, Linearorder
    -   [X] Dedekind completion of Preorders
-   Analysis
    -   [ ] Definition of continuous functions on ℝ
    -   [ ] Proof of equivalence with topological continuity
-   Spaces
    -   Topological
        -   [ ] Topology/Locale "on" ℝ
        -   [ ] Proof of compactness of interval
-   Category theory
    -   Setoid based 1-category theory
        -   [X] Definition of Category, Functor, Natural transformation
        -   [X] Definition of Monad, Kleisli category
        -   [X] Yoneda lemma
        -   [ ] Limits
            -   [ ] Specific
                -   [X] Coequalizer
                -   [ ] [REW] Others
            -   [ ] [REW] Definition as Kan extensions
    -   (∞,1)-category theory
        -   [ ] Via simplicial sets
-   Formal systems
    -   Theory of Computational problems
        -   [X] Category of problems
        -   [ ] Specific
            -   [ ] [WIP] Unification
            -   [ ] Generic parsing
            -   [ ] Generic type checking
    -   Type theories
        -   [ ] Specific
            -   [X] Implementation of Church-style λ-Calculus (Type checking, evaluation)
            -   [ ] [WIP] Implementation of Curry-style λ-Calculus (Type checking)
            -   [ ] [WIP] Implementation of Hindley-Milner type system (Type checking)
        -   [ ] Generic definition of the concept of a "type theory"


<a id="org3cd892c"></a>

### Concerning execution of the code

-   Custom build system
    -   [X] Compilation of Agda code as a haskell-stack project
    -   [X] Interdependency between Agda and Haskell source code
-   Supporting haskell code
    -   [ ] Parsing of lambda calculus terms into AST


<a id="orgdd84ff6"></a>

### Concerning compilation to pdf

-   [ ] Support for compilation to pdf in build system
-   [ ] Prettifying the output

