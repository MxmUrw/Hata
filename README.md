
# Table of Contents

1.  [旗企画 「Project Hata」](#orgb9407e4)
    1.  [Goal](#org2da78f5)
    2.  [Current state](#orgcbef6fb)
        1.  [Concerning formalization of mathematics](#orgfab47c4)
        2.  [Concerning execution of the code](#orgd583ffc)
        3.  [Concerning compilation to pdf](#org89e0076)


<a id="orgb9407e4"></a>

# 旗企画 「Project Hata」


<a id="org2da78f5"></a>

## Goal

The ambitious goal of this project is to formalize enough mathematics (category theory, algebra) to
be able to do proper verified development of theoretical computer science, i.e., type theory,
logic, algorithms, compilation.

The philosophy of the formalization is that 3 aspects should be accommodated with as few
compromises as possible:

-   The code should compile into a native binary.
-   The code should also be compilable into a pdf file, producing a mathematical document akin to the ones
    written by hand.
-   Finally the source files itself should remain humanly readable, i.e. all commentary intended for the pdf should
    be formatted without much syntactic overhead. This means that a markdown-like language is more preferrable
    than e.g. Tex.


<a id="orgcbef6fb"></a>

## Current state

In the following the current state of different features is shown.
Explanation of the checkboxes:

-   [X] A checked box means that this topic is implemented.
    (with a certain amount of corresponding proofs which would usually be expected)
-   [ ] An unchecked box means that this topic is not implemented yet,
    but is considered for future implementation.
-   [ ] [REW/WIP] An unchecked box with an annotation means that this topic is currently in development (WIP), or that it
    once was implemented, but is currently pending a rewrite (REW) (being out of date because of rewrites in other places).


<a id="orgfab47c4"></a>

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


<a id="orgd583ffc"></a>

### Concerning execution of the code

-   Custom build system
    -   [ ] Compilation of Agda code as a haskell-stack project
    -   [ ] Interdependency between Agda and Haskell source code
-   Supporting haskell code
    -   [ ] Parsing of lambda calculus terms into AST


<a id="org89e0076"></a>

### Concerning compilation to pdf

-   [ ] Support for compilation to pdf in build system
-   [ ] Prettifying the output

