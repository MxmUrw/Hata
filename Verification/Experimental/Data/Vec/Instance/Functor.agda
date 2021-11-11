
module Verification.Core.Data.Vec.Instance.Functor where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Functor.Instance.Category
-- open import Verification.Core.Category.Std.Natural.Definition
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Monad.Definition

open import Verification.Core.Data.Universe.Everything
-- open import Verification.Core.Category.Std.Monad.TypeMonadNotation

private
  lem-1 : ∀{n} -> {A B C : 𝒰 𝑖} -> {f : A -> B} -> {g : B -> C}
          -> ∀(as : Vec A n) -> map-Vec (g ∘ f) as ≡ map-Vec g (map-Vec f as)
  lem-1 [] = refl-≡
  lem-1 {f = f} {g} (x ∷ as) = λ i → g (f x) ∷ lem-1 {f = f} {g} as i


instance
  isFunctor:Vec : ∀{n} -> isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) (λ a -> Vec a n)
  isFunctor.map isFunctor:Vec = map-Vec
  isFunctor.isSetoidHom:map isFunctor:Vec = {!!}
  isFunctor.functoriality-id isFunctor:Vec = {!!}
  isFunctor.functoriality-◆ isFunctor:Vec = funExt lem-1




