
module Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.Functor where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition



module _ {𝒞 : Category 𝑖} where
  module _ {F G : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)} where
    mapᵘ-⨊ᵒᵖ : Natural F G -> (⨊ᵒᵖ F) -> (⨊ᵒᵖ G)
    mapᵘ-⨊ᵒᵖ α (a , a⃩) = a , ⟨ ⟨ α ⟩ ⟩ a⃩


    -- module _ (α : Natural F G) where
    --   macro map-⨊ᵒᵖ = #structureOn (mapᵘ-⨊ᵒᵖ α)

    module _ {α : Natural F G} where
      map-map-⨊ᵒᵖ : {a b : ⨊ᵒᵖ F} -> a ⟶ b -> mapᵘ-⨊ᵒᵖ α a ⟶ mapᵘ-⨊ᵒᵖ α b
      map-map-⨊ᵒᵖ (f , f⃩) = f , {!!}

      instance
        isFunctor:mapᵘ-⨊ᵒᵖ : isFunctor (⨊ᵒᵖ F) (⨊ᵒᵖ G) (mapᵘ-⨊ᵒᵖ α)
        isFunctor.map isFunctor:mapᵘ-⨊ᵒᵖ = map-map-⨊ᵒᵖ
        isFunctor.isSetoidHom:map isFunctor:mapᵘ-⨊ᵒᵖ = {!!}
        isFunctor.functoriality-id isFunctor:mapᵘ-⨊ᵒᵖ = {!!}
        isFunctor.functoriality-◆ isFunctor:mapᵘ-⨊ᵒᵖ = {!!}

    module _ (α : Natural F G) where
      macro map-⨊ᵒᵖ = #structureOn (mapᵘ-⨊ᵒᵖ α)

    module _ (α : Natural F G) where
      map-⨊ᵒᵖ' : Functor (⨊ᵒᵖ F) (⨊ᵒᵖ G)
      map-⨊ᵒᵖ' = mapᵘ-⨊ᵒᵖ α since isFunctor:mapᵘ-⨊ᵒᵖ {α = α}


