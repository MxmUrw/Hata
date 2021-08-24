
module Verification.Experimental.Category.Std.Functor.Adjoint.Property.Base where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Notation.Associativity

open import Verification.Experimental.Category.Std.Functor.Adjoint.Definition

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} {{_ : F ⊣ G}} where
    module _ {a b : ⟨ 𝒞 ⟩} {c : ⟨ 𝒟 ⟩} where
      module _ {f g : a ⟶ b} {h i : ⟨ F ⟩ b ⟶ c} where
        construct-postcomp-cofree : map f ◆ h ∼ map g ◆ i -> f ◆ cofree h ∼ g ◆ cofree i
        construct-postcomp-cofree p = p
                 >> map f ◆ h ∼ map g ◆ i <<
                 ⟪ cong-∼ ⟫
                 >> map (map f ◆ h) ∼ map (map g ◆ i) <<
                 ⟪ functoriality-◆ ≀∼≀ functoriality-◆ ⟫
                 >> map (map f) ◆ map h ∼ map (map g) ◆ map i <<
                 ⟪ (refl ◈_) ⟫
                 >> coadj ◆ (map (map f) ◆ map h) ∼ coadj ◆ (map (map g) ◆ map i) <<
                 ⟪ assoc-r-◆ ≀∼≀ assoc-r-◆ ⟫
                 >> (coadj ◆ map (map f)) ◆ map h ∼ (coadj ◆ map (map g)) ◆ map i <<
                 ⟪ naturality f ◈ refl ≀∼≀ naturality g ◈ refl ⟫
                 >> (f ◆ coadj) ◆ map h ∼ (g ◆ coadj) ◆ map i <<
                 ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫

    -- module _ {a : ⟨ 𝒞 ⟩} {b c : ⟨ 𝒟 ⟩} where
    --   module _ {f : a ⟶ ⟨ G ⟩ b} {g h : b ⟶ c} where
    --     destruct-precomp-free : (free f ◆ g ∼ free f ◆ h) -> f ◆ map g ∼ f ◆ map h
    --     destruct-precomp-free p = p₀
    --       where
    --         p₀ = p
    --              >> free f ◆ g ∼ free f ◆ h <<

    --              ⟪ cong-∼ ⟫

    --              -- >> map (free f ◆ g) ∼ map (free f ◆ h) <<

    --              ⟪ functoriality-◆ ≀∼≀ functoriality-◆ ⟫

    --              -- >> map (free f) ◆ map g ∼ map (free f) ◆ map h <<

    --              -- >> map (map f ◆ adj) ◆ map g ∼ map (map f ◆ adj) ◆ map h <<

    --              ⟪ functoriality-◆ ◈ refl ≀∼≀
    --                functoriality-◆ ◈ refl ⟫

    --              -- >> map (map f) ◆ map adj ◆ map g ∼ map (map f) ◆ map adj ◆ map h <<

    --              ⟪ refl ◈_ ⟫

    --              -- >> coadj ◆ (map (map f) ◆ map adj ◆ map g) ∼ coadj ◆ (map (map f) ◆ map adj ◆ map h) <<

    --              ⟪ assoc-[abcd]∼a[bcd]-◆ ⁻¹ ≀∼≀
    --                assoc-[abcd]∼a[bcd]-◆ ⁻¹ ⟫

    --              -- >> coadj ◆ map (map f) ◆ map adj ◆ map g ∼ coadj ◆ map (map f) ◆ map adj ◆ map h <<

    --              ⟪ naturality f ◈ refl ◈ refl ≀∼≀
    --                naturality f ◈ refl ◈ refl ⟫

    --              -- >> f ◆ coadj ◆ map adj ◆ map g ∼ f ◆ coadj ◆ map adj ◆ map h <<

    --              ⟪ assoc-[abcd]∼a[bc]d-◆ ≀∼≀
    --                assoc-[abcd]∼a[bc]d-◆ ⟫

    --              -- >> f ◆ (coadj ◆ map adj) ◆ map g ∼ f ◆ (coadj ◆ map adj) ◆ map h <<

    --              ⟪ refl ◈ reduce-coadj ◈ refl ≀∼≀
    --                refl ◈ reduce-coadj ◈ refl ⟫

    --              -- >> f ◆ id ◆ map g ∼ f ◆ id ◆ map h <<

    --              ⟪ unit-r-◆ ◈ refl ≀∼≀
    --                unit-r-◆ ◈ refl ⟫

    --              >> f ◆ map g ∼ f ◆ map h <<
