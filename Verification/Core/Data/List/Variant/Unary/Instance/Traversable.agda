
module Verification.Core.Data.List.Variant.Unary.Instance.Traversable where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category

open import Verification.Core.Category.Std.Monad.Definition

open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Monad.TypeMonadNotation

-- instance
--   isFunctor:List : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) List
--   isFunctor.map isFunctor:List = map-List
--   isFunctor.isSetoidHom:map isFunctor:List = {!!}
--   isFunctor.functoriality-id isFunctor:List = {!!}
--   isFunctor.functoriality-◆ isFunctor:List = {!!}

instance
  isTraversable:List : isTraversable ′(List {𝑖})′
  isTraversable:List {𝑖} = traversable (λ {M} {{MM}} {A} xs -> f {M} {MM} {A} xs)
    where
      module _ {M : 𝒰' 𝑖 → 𝒰' 𝑖} { MM : Monad ′ 𝒰' 𝑖 ′ on M } where
          f : {A : 𝒰' 𝑖} → List (M A) → M (List A)
          f [] = return []
          f (x ∷ xs) = do
            x <- x
            xs <- f xs
            return (x ∷ xs)

module _ {A : 𝒰 𝑖} where
  join-List : List (List A) -> List A
  join-List ⦋⦌ = []
  join-List (xs ∷ xss) = xs ⋆ join-List xss

  pure-List : A -> List A
  pure-List a = a ∷ []


module _ {A : 𝒰 𝑖} where
  List→Vec : List A -> ∑ Vec A
  List→Vec [] = zero , []
  List→Vec (x ∷ xs) = _ , x ∷ List→Vec xs .snd

  Vec→List : Vec A n -> List A
  Vec→List ⦋⦌ = []
  Vec→List (x ∷ xs) = x ∷ Vec→List xs



