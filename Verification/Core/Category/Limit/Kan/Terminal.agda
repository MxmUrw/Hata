
module Verification.Core.Category.Limit.Kan.Terminal where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Lift


--------------------------------------------------------------------
-- Terminal object

-- [Definition]
-- | We call an object terminal if ...
record ITerminal (X : Category 𝑖) (x : ⟨ X ⟩) : 𝒰 (𝑖 ⁺) where
  field ! : ∀(a : ⟨ X ⟩) -> Hom a x
        unique : ∀{a : ⟨ X ⟩} -> (f : Hom a x) -> f ≣ ! a
open ITerminal {{...}} public
unquoteDecl Terminal terminal = #struct "Term" (quote ITerminal) "x" Terminal terminal
-- //

-- [Notation]
-- | We write |𝟙| for the terminal object of a category, if it exists.
𝟙 : {X : 𝒰 𝑖} {{_ : isCategory X 𝑗}} {{_ : Terminal (⩚ X)}} -> X
𝟙 {{_}} {{t}} = ⟨ t ⟩
-- //



--------------------------------------------------------------------
-- Cat has terminal object

-- [Example]
-- | The discrete category on |⊤| is a terminal object of Cat
-- | For this, we define it by:
Category:𝟙 : Category _
Category:𝟙 = Category:Discrete 𝟙-𝒰

instance isCategory:𝟙 = #openstruct Category:𝟙

-- | And now we show that it is indeed terminal.
private
  module _ {𝒞 : Category 𝑖} where
    !-Cat : 𝒞 ⟶ ↑ Category:𝟙
    ⟨ !-Cat ⟩ _ = ↥ tt
    IFunctor.map (of !-Cat) _ = ↥ id
    IFunctor.functoriality-id (of !-Cat) = ↥ refl
    IFunctor.functoriality-◆ (of !-Cat) = ↥ refl
    IFunctor.functoriality-≣ (of !-Cat) p = ↥ refl

    unique::!-Cat : ∀(F G : 𝒞 ⟶ ↑ Category:𝟙) -> F ≣ G
    unique::!-Cat F G = record { object-path = refl ; arrow-path = λ f -> ↥ (P₀ _ _) }
      where P₀ : ∀{a b : 𝟙-𝒰} -> (f g : Hom a b) -> f ≣ g
            P₀ {tt} {.tt} id-Q id-Q = refl
            P₀ {a} {.a} id-Q (some (last ()))
            P₀ {a} {.a} id-Q (some (() ∷ x₁))
            P₀ {a} {b} (some (last ())) g
            P₀ {a} {b} (some (() ∷ x₁)) g

instance
  Terminal:Category : Terminal (Category:Category 𝑖)
  ⟨ Terminal:Category ⟩ = ↑ Category:𝟙
  ITerminal.! (of Terminal:Category) _ = !-Cat
  ITerminal.unique (of Terminal:Category) F = unique::!-Cat _ _

instance ITerminal:Category = #openstruct Terminal:Category
-- //


