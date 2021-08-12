
module Verification.Experimental.Category.Std.Functor.Adjoint where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Notation.Associativity


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isAdjoint (F : Functor 𝒞 𝒟) (G : Functor 𝒟 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field adj    : ∀{a : ⟨ 𝒟 ⟩} -> ⟨ F ⟩ (⟨ G ⟩ a) ⟶ a
    field coadj  : ∀{a : ⟨ 𝒞 ⟩} -> a ⟶ ⟨ G ⟩ (⟨ F ⟩ a)
    field {{isNatural:adj}} : isNatural (G ◆-𝐂𝐚𝐭 F) id adj
    field {{isNatural:coadj}} : isNatural id (F ◆-𝐂𝐚𝐭 G) coadj
    field reduce-coadj : ∀{b : ⟨ 𝒟 ⟩}  -> coadj ◆ map adj ∼ id {a = ⟨ G ⟩ b}
    field reduce-adj : ∀{a : ⟨ 𝒞 ⟩}    -> map coadj ◆ adj ∼ id {a = ⟨ F ⟩ a}

  open isAdjoint {{...}} public


  module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} {{_ : isAdjoint F G}} where

    -- |> For any two objects [..] and [..],
    module _ {a : ⟨ 𝒞 ⟩} {b : ⟨ 𝒟 ⟩} where

      -- |> we have an isomorphism between hom-types as follows:
      free : (a ⟶ ⟨ G ⟩ b) -> (⟨ F ⟩ a ⟶ b)
      free f = map f ◆ adj

      -- | The inverse direction is given by:
      cofree : (⟨ F ⟩ a ⟶ b) -> (a ⟶ ⟨ G ⟩ b)
      cofree f = coadj ◆ map f

    module _ {a : ⟨ 𝒞 ⟩} {b c : ⟨ 𝒟 ⟩} where
      module _ {f : a ⟶ ⟨ G ⟩ b} {g h : b ⟶ c} where
        destruct-precomp-free : (free f ◆ g ∼ free f ◆ h) -> f ◆ map g ∼ f ◆ map h
        destruct-precomp-free p = p₀
          where
            p₀ = p
                 >> free f ◆ g ∼ free f ◆ h <<

                 ⟪ cong-∼ ⟫

                 -- >> map (free f ◆ g) ∼ map (free f ◆ h) <<

                 ⟪ functoriality-◆ ≀∼≀ functoriality-◆ ⟫

                 -- >> map (free f) ◆ map g ∼ map (free f) ◆ map h <<

                 -- >> map (map f ◆ adj) ◆ map g ∼ map (map f ◆ adj) ◆ map h <<

                 ⟪ functoriality-◆ ◈ refl ≀∼≀
                   functoriality-◆ ◈ refl ⟫

                 -- >> map (map f) ◆ map adj ◆ map g ∼ map (map f) ◆ map adj ◆ map h <<

                 ⟪ refl ◈_ ⟫

                 -- >> coadj ◆ (map (map f) ◆ map adj ◆ map g) ∼ coadj ◆ (map (map f) ◆ map adj ◆ map h) <<

                 ⟪ assoc-[abcd]∼a[bcd]-◆ ⁻¹ ≀∼≀
                   assoc-[abcd]∼a[bcd]-◆ ⁻¹ ⟫

                 -- >> coadj ◆ map (map f) ◆ map adj ◆ map g ∼ coadj ◆ map (map f) ◆ map adj ◆ map h <<

                 ⟪ naturality f ◈ refl ◈ refl ≀∼≀
                   naturality f ◈ refl ◈ refl ⟫

                 -- >> f ◆ coadj ◆ map adj ◆ map g ∼ f ◆ coadj ◆ map adj ◆ map h <<

                 ⟪ assoc-[abcd]∼a[bc]d-◆ ≀∼≀
                   assoc-[abcd]∼a[bc]d-◆ ⟫

                 -- >> f ◆ (coadj ◆ map adj) ◆ map g ∼ f ◆ (coadj ◆ map adj) ◆ map h <<

                 ⟪ refl ◈ reduce-coadj ◈ refl ≀∼≀
                   refl ◈ reduce-coadj ◈ refl ⟫

                 -- >> f ◆ id ◆ map g ∼ f ◆ id ◆ map h <<

                 ⟪ unit-r-◆ ◈ refl ≀∼≀
                   unit-r-◆ ◈ refl ⟫

                 >> f ◆ map g ∼ f ◆ map h <<











