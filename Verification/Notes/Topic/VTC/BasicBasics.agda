
module Verification.Notes.Topic.VTC.BasicBasics where

-- [Hide]
open import Verification.Conventions
  hiding
    ( ⊤-𝒰
    ; ⊥-𝒰
    ; _+-𝒰_
    ; _×-𝒰_
    )

-- //

-- | Proving theorems in Agda follows
--   the /propositions as types/ principle, see for example \cite{TT:Wadler:2015}.
--   Succinctly, the idea is that types are not only used
--   to describe the structure of data, in the way that
--   types like |Int|, |Float| or |String| might be used in other programming
--   languages; They are also used to describe propositions, such
--   as |1 < 2|. The idea is that such a type |1 < 2| is defined in a way
--   that constructing an element of it actually amounts to a proof of that proposition.
--   Oftentimes propositions like this can be constructed inductively, by listing
--   the constructors from which proofs of the proposition can be freely generated.
--   We call the elements of a type also /inhabitants/.

private
-- | We denote the type of types by |𝒰|, short for /universe/. Let us now
--   introduce some common types which are used in the remainder of the thesis.
-- | The /bottom type/ [..] is defined as a data type without constructors. It can be
--   used to denote falsehood.
  data ⊥-𝒰 : 𝒰₀ where
-- | The /top type/ [..],
  data ⊤-𝒰 : 𝒰₀ where
  -- |> is defined as a data type with a single constructor [..].
    tt : ⊤-𝒰
    -- |> As a proposition, it may be interpreted as always true.

-- | The /sum type/ |A +-𝒰 B| of two types |A| and |B|
--   is given by the following data type:
  data _+-𝒰_ (A B : 𝒰₀) : 𝒰₀ where
    -- |> It has two constructors:
    left : A -> A +-𝒰 B
    right : B -> A +-𝒰 B
    -- |> From a logical point of view it is used as the statement that either |A| or |B|
    --   holds.

-- | Conjunction is expressed by the /product type/ |A ×-𝒰 B|, with
--   two projection functions |fst : A ×-𝒰 B → A| and |snd : A ×-𝒰 B → B|.
--   In Agda, it is usually defined as a record type [..] with two fields.
--   To construct an inhabitant of a record type, values for all fields need to be provided.
--   We thus usually describe records similar to the following: In order to construct
--   an element of |A ×-𝒰 B|, the following data must be given:
record _×-𝒰_ (A B : 𝒰₀) : 𝒰₀ where
  -- | 1. A value [..].
  field fst : A
  -- | 2. A value [..].
  field snd : B
-- |: The names of the fields then also take on the role of the projection functions.

-- | A type family |P : A → 𝒰| describes a predicate on |A|. Quantification
--   can then be done by using dependent product or dependent sum types.
--   An inhabitant of the /dependent sum/ |∑[ a : A ] (P a)| proves that there
--   exists an |a : A| such that |P a| holds. Such an inhabitant is given by
--   a tuple |(a , p)|, where |a : A| and |p : P a| is a proof that the predicate actually holds for |a|.

private variable A : 𝒰₀

-- | Let [..] be a predicate on |A|. We call |P| usually a /type family/ on |A|.
module _ (P : A -> 𝒰₀) where
  -- |> The /dependent product/ has as inhabitants functions which, for every |a : A|
  --    give a proof of |P a|. All of the following notations are possible:
  -- [Hide]
    postulate
  -- //
      f : (a : A) -> P a
      g : ∀ (a : A) -> P a
      h : ∀(a : A) -> P a
-- | Furthermore, Agda has a feature called /implicit function arguments/,
--   which allows us to declare that the argument of the function needs not
--   to be explicitly given when that function is called. Agda then tries to infer
--   it from the context. To denote this,
--   curly braces are used, e.g.:
      i : {a : A} -> P a

-- [Remark]
-- | There is a difference between the classical notion of /proposition/
--   and of types as used in Agda. Classically, there is no difference between
--   different proofs of the same proposition. In a theory like Agda, the
--   proof is a term like any other term. And thus proofs may be compared with each other.
--   This has various consequences\cite{TT:HoTTBook:2013}, but very rarely was of concern in the development
--   of the present thesis.

-- //

-- | For equality, we use both the path based equality |a ≡ b| of cubical Agda,
--   as well as the usual inductively defined one, which we denote by |a ≣ b|.
--   The proof of reflexivity is denoted by |refl-≡ : a ≡ a| and |refl-≣ : a ≣ a|,
--   respectively. For symmetry and transitivity similar names based on |sym| and |trans| are
--   used.

-- [Remark]
-- | These types of equality can be shown to be equivalent, yet oftentimes there are situations
--   in which either one of them is preferrable. Using the concepts of setoids,
--   we usually abstract over the kind of equality, except when working with concrete
--   types. The drawback of this liberal attitude is that, when both of the above
--   definitions of equality appear in the same context, conversion between them
--   are necessary.

-- //

-- [Remark]
-- | The fact that we use the cubical version of Agda \cite{Agda:Cubical} has not many implications,
--   since none of the advanced concepts such as univalence or quotient types
--   are necessary. With the exception of functional extensionality,
--   which is very convenient.

-- //



