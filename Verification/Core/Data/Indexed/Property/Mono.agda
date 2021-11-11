
module Verification.Core.Data.Indexed.Property.Mono where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Contradiction
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Data.Universe.Instance.Category

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Indexed.Definition



module _ {𝒞 : Category 𝑖} {I : 𝒰 𝑗} where
  module _ {a b : 𝐈𝐱 I 𝒞} {ϕ : a ⟶ b} where
    construct-isMono-𝐈𝐱 : (∀ {i} -> isMono (ϕ i)) -> (isMono ϕ)
    isMono.cancel-mono (construct-isMono-𝐈𝐱 P) {z} {α} {β} x i = cancel-mono (x i)
      where
        instance _ = P {i}



-- Here we prove that if an arrow in 𝐈𝐱 I 𝒞 is monic, than all its parts are.
-- For this we do need to know that I is discrete in order to be able to construct
-- objects / morphisms which behave differently at different i


module _ {𝒞 : Category 𝑖} {I : 𝒰 𝑗} {{_ : isDiscrete I}} where
  private

    homix : ∀{a b : 𝐈𝐱 I 𝒞} (ϕ : a ⟶ b) -> (a ⟶ b)
    homix ϕ = ϕ

    lift-obj : (a : ⟨ 𝒞 ⟩) -> (i : I) -> (def : 𝐈𝐱 I 𝒞)-> 𝐈𝐱 I 𝒞
    lift-obj a i def = indexed f
      where
        f : I -> ⟨ 𝒞 ⟩
        f j with (i ≟-Str j)
        ... | yes p = a
        ... | no ¬p = ix def j

    lift-hom : ∀{a : ⟨ 𝒞 ⟩} {b : 𝐈𝐱 I 𝒞} -> {i : I} -> a ⟶ ix b i -> lift-obj a i b ⟶ b
    lift-hom {i = i} f j with i ≟-Str j
    ... | yes refl-≣ = f
    ... | no ¬p = id

    lem-1 : ∀{a : ⟨ 𝒞 ⟩} {b : 𝐈𝐱 I 𝒞} -> {i j : I} -> i ≣ j -> (ξ ζ : a ⟶ ix b i) -> lift-hom {a = a} {b = b} {i = i} ξ j ∼ lift-hom ζ j -> ξ ∼ ζ
    lem-1 {i = i} {j} p ξ ζ q with i ≟-Str j
    ... | yes refl-≣ = q
    ... | no ¬p = impossible (¬p p)

  module _ {a b : 𝐈𝐱 I 𝒞} {ϕ : a ⟶ b} where
    destruct-isMono-𝐈𝐱 : (isMono {𝒞 = 𝐈𝐱 I 𝒞} ϕ) -> (∀ {i} -> isMono (ϕ i))
    isMono.cancel-mono (destruct-isMono-𝐈𝐱 p {i}) {z} {α} {β} αϕ∼βϕ = P₂
      where
        instance
          _ = p

        α' : lift-obj z i a ⟶ a
        α' = lift-hom α

        β' : lift-obj z i a ⟶ a
        β' = lift-hom β

        P₀ : α' ◆ ϕ ∼ β' ◆ ϕ
        P₀ k with i ≟-Str k
        ... | yes refl-≣  = αϕ∼βϕ
        ... | no ¬p       = refl

        P₁ : α' ∼ β'
        P₁ = cancel-mono P₀

        P₂ : α ∼ β
        P₂ = lem-1 refl-≣ α β (P₁ i)



