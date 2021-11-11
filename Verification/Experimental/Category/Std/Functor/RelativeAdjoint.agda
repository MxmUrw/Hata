
module Verification.Core.Category.Std.Functor.RelativeAdjoint where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where

  record isRelativeAdjoint (J : Functor 𝒞 ℰ) (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    field refree : ∀{a : ⟨ 𝒞 ⟩} {b : ⟨ 𝒟 ⟩} -> ⟨ J ⟩ a ⟶ ⟨ G ⟩ b -> ⟨ F ⟩ a ⟶ b
    field recofree : ∀{a : ⟨ 𝒞 ⟩} {b : ⟨ 𝒟 ⟩} -> ⟨ F ⟩ a ⟶ b -> ⟨ J ⟩ a ⟶ ⟨ G ⟩ b


--     field adj    : ∀{a : ⟨ 𝒟 ⟩} -> ⟨ F ⟩ (⟨ G ⟩ a) ⟶ a
--     field coadj  : ∀{a : ⟨ 𝒞 ⟩} -> a ⟶ ⟨ G ⟩ (⟨ F ⟩ a)
--     field {{isNatural:adj}} : isNatural (G ◆-𝐂𝐚𝐭 F) id adj
--     field {{isNatural:coadj}} : isNatural id (F ◆-𝐂𝐚𝐭 G) coadj
--     field reduce-coadj : ∀{b : ⟨ 𝒟 ⟩}  -> coadj ◆ map adj ∼ id {a = ⟨ G ⟩ b}
--     field reduce-adj : ∀{a : ⟨ 𝒞 ⟩}    -> map coadj ◆ adj ∼ id {a = ⟨ F ⟩ a}

  open isRelativeAdjoint {{...}} public


  module _ {J : Functor 𝒞 ℰ} {F : Functor 𝒞 𝒟} {G : Functor 𝒟 ℰ} {{_ : isRelativeAdjoint J F G}} where

    module _ {a : ⟨ 𝒞 ⟩} {b c : ⟨ 𝒟 ⟩} where
      module _ {f₀ f₁ : ⟨ J ⟩ a ⟶ ⟨ G ⟩ b} {g₀ g₁ : b ⟶ c} where
        destruct-precomp-free : (refree f₀ ◆ g₀ ∼ refree f₁ ◆ g₁) -> f₀ ◆ map g₀ ∼ f₁ ◆ map g₁
        destruct-precomp-free p = {!!}

        construct-precomp-free : f₀ ◆ map g₀ ∼ f₁ ◆ map g₁ -> (refree f₀ ◆ g₀ ∼ refree f₁ ◆ g₁)
        construct-precomp-free = {!!}
        -- p₀
--           where
--             p₀ = p
--                  >> free f ◆ g ∼ free f ◆ h <<

--                  ⟪ cong-∼ ⟫

--                  -- >> map (free f ◆ g) ∼ map (free f ◆ h) <<

--                  ⟪ functoriality-◆ ≀∼≀ functoriality-◆ ⟫

--                  -- >> map (free f) ◆ map g ∼ map (free f) ◆ map h <<

--                  -- >> map (map f ◆ adj) ◆ map g ∼ map (map f ◆ adj) ◆ map h <<

--                  ⟪ functoriality-◆ ◈ refl ≀∼≀
--                    functoriality-◆ ◈ refl ⟫

--                  -- >> map (map f) ◆ map adj ◆ map g ∼ map (map f) ◆ map adj ◆ map h <<

--                  ⟪ refl ◈_ ⟫

--                  -- >> coadj ◆ (map (map f) ◆ map adj ◆ map g) ∼ coadj ◆ (map (map f) ◆ map adj ◆ map h) <<

--                  ⟪ assoc-[abcd]∼a[bcd]-◆ ⁻¹ ≀∼≀
--                    assoc-[abcd]∼a[bcd]-◆ ⁻¹ ⟫

--                  -- >> coadj ◆ map (map f) ◆ map adj ◆ map g ∼ coadj ◆ map (map f) ◆ map adj ◆ map h <<

--                  ⟪ naturality f ◈ refl ◈ refl ≀∼≀
--                    naturality f ◈ refl ◈ refl ⟫

--                  -- >> f ◆ coadj ◆ map adj ◆ map g ∼ f ◆ coadj ◆ map adj ◆ map h <<

--                  ⟪ assoc-[abcd]∼a[bc]d-◆ ≀∼≀
--                    assoc-[abcd]∼a[bc]d-◆ ⟫

--                  -- >> f ◆ (coadj ◆ map adj) ◆ map g ∼ f ◆ (coadj ◆ map adj) ◆ map h <<

--                  ⟪ refl ◈ reduce-coadj ◈ refl ≀∼≀
--                    refl ◈ reduce-coadj ◈ refl ⟫

--                  -- >> f ◆ id ◆ map g ∼ f ◆ id ◆ map h <<

--                  ⟪ unit-r-◆ ◈ refl ≀∼≀
--                    unit-r-◆ ◈ refl ⟫

--                  >> f ◆ map g ∼ f ◆ map h <<






