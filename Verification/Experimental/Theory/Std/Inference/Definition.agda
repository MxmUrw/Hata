
module Verification.Experimental.Theory.Std.Inference.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition



-- module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
--   module _ {A : 𝒰 𝑖} where
--     ⨆ᶠ : ∀{as : 人List A} -> ([ as ]ᶠ -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
--     ⨆ᶠ = {!!}


-- module _ {𝒞 : Category 𝑖} where
--   instance
--     isCategory:Monad : isCategory {⨆ 𝑖 , ⨆ 𝑖} (Monad 𝒞)
--     isCategory:Monad = {!!}

module _ (𝒞 : Category 𝑖) where
  macro 𝐌𝐧𝐝 = #structureOn (Monad 𝒞)

module _ {I : 𝒰 𝑖} where
  instance
    isCategory:FinitaryRelativeMonad : isCategory {𝑖 , 𝑖} (FinitaryRelativeMonad I)
    isCategory:FinitaryRelativeMonad = {!!}

module _ (I : 𝒰 𝑖) where
  macro 𝐅𝐢𝐧𝐑𝐞𝐥𝐌𝐧𝐝 = #structureOn (FinitaryRelativeMonad I)


𝑖𝑥mnd : 𝒰 𝑖 -> Category _
𝑖𝑥mnd {𝑖} I = 𝐅𝐢𝐧𝐑𝐞𝐥𝐌𝐧𝐝 (I)

map-𝑖𝑥mnd : ∀{a b : 𝒰 𝑖} -> (a → b) → Functor (𝑖𝑥mnd b) (𝑖𝑥mnd a)
map-𝑖𝑥mnd = {!!}

instance
  isFunctor:𝑖𝑥mnd : isFunctor (𝐔𝐧𝐢𝐯 𝑖 ᵒᵖ) (𝐂𝐚𝐭 _) 𝑖𝑥mnd
  isFunctor.map isFunctor:𝑖𝑥mnd = map-𝑖𝑥mnd
  isFunctor.isSetoidHom:map isFunctor:𝑖𝑥mnd = {!!}
  isFunctor.functoriality-id isFunctor:𝑖𝑥mnd = {!!}
  isFunctor.functoriality-◆ isFunctor:𝑖𝑥mnd = {!!}

{-
module _ (𝑖 : 𝔏) where
  𝐈𝐱𝐌𝐧𝐝ᵘ : 𝒰 _
  𝐈𝐱𝐌𝐧𝐝ᵘ = ⨊ᵒᵖ ′ 𝑖𝑥mnd {𝑖} ′

  macro 𝐈𝐱𝐌𝐧𝐝 = #structureOn 𝐈𝐱𝐌𝐧𝐝ᵘ


open import Agda.Primitive using (lsuc)

module _ (J : 𝒰 𝑗) where
  record hasPseudoInverse2 {𝑖 : 𝔏} (a b : 𝐈𝐱𝐌𝐧𝐝 𝑖) : 𝒰 (join-𝔏 (𝑖 ⁺) 𝑗) where
    -- field testaa : (Indexed (J) (𝒰 𝑖 since isCategory:𝒰)) -> (Indexed (J) (𝒰 𝑖 since {!!}))
    field PIErr : Functor (𝐈𝐱 (base a) (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖))

-- module _ (J : 𝒰 𝑗) where
--   record hasPseudoInverse {𝑖 : 𝔏} {a b : 𝐈𝐱𝐌𝐧𝐝 𝑖} (f : a ⟶ b) : 𝒰 (join-𝔏 (lsuc 𝑖) 𝑗) where
--     field testaa : (Indexed (J) (𝒰 𝑖 since isCategory:𝒰)) -> (Indexed (J) (𝒰 𝑖 since {!!}))
--     -- field PIErr : Functor (𝐈𝐱 (base b) (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 (base b) (𝐔𝐧𝐢𝐯 𝑖))


-}
-- 𝐈𝐧𝐟



