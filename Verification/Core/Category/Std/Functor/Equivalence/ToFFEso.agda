
module Verification.Core.Category.Std.Functor.Equivalence.ToFFEso where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Set.Setoid.Morphism
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Equivalence.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  module _ {F : Functor 𝒞 𝒟} {{ofF : isIso-𝐂𝐚𝐭 F}} where
    private
      G : Functor 𝒟 𝒞
      G = inverse-◆-𝐂𝐚𝐭 ofF

      ϕ : ∀{a : ⟨ 𝒞 ⟩} -> ⟨ G ⟩ (⟨ F ⟩ a) ≅ a
      ϕ = ⟨ ⟨ inv-r-◆-𝐂𝐚𝐭 (ofF) ⟩ ⟩ _ since record
        { inverse-◆ = ⟨ ⟨ inv-r-◆-𝐂𝐚𝐭 ofF ⟩⁻¹ ⟩ _
        ; inv-r-◆ = ⟨ inv-r-◆ (of inv-r-◆-𝐂𝐚𝐭 ofF) ⟩ _
        ; inv-l-◆ = ⟨ inv-l-◆ (of inv-r-◆-𝐂𝐚𝐭 ofF) ⟩ _
        }

      ψ : ∀{a : ⟨ 𝒟 ⟩} -> ⟨ F ⟩ (⟨ G ⟩ a) ≅ a
      ψ = ⟨ ⟨ inv-l-◆-𝐂𝐚𝐭 (ofF) ⟩ ⟩ _ since record
        { inverse-◆ = ⟨ ⟨ inv-l-◆-𝐂𝐚𝐭 ofF ⟩⁻¹ ⟩ _
        ; inv-r-◆ = ⟨ inv-r-◆ (of inv-l-◆-𝐂𝐚𝐭 ofF) ⟩ _
        ; inv-l-◆ = ⟨ inv-l-◆ (of inv-l-◆-𝐂𝐚𝐭 ofF) ⟩ _
        }

      --
      -- First, we show that both F and G are faithful
      --
      module _ {a b : ⟨ 𝒞 ⟩} where
        cancel-injective-F : {f g : a ⟶ b} -> map f ∼ map g -> f ∼ g
        cancel-injective-F {f} {g} p =

          f

          ⟨ unit-l-◆ ⁻¹ ⟩-∼

          id ◆ f

          ⟨ inv-l-◆ (of ϕ) ⁻¹ ◈ refl ⟩-∼

          ⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩ ◆ f

          ⟨ assoc-l-◆ ⟩-∼

          ⟨ ϕ ⟩⁻¹ ◆ (⟨ ϕ ⟩ ◆ f)

          ⟨ refl ◈ naturality f ⟩-∼

          ⟨ ϕ ⟩⁻¹ ◆ (mapOf (F ◆-𝐂𝐚𝐭 G) f ◆ ⟨ ϕ ⟩)

          ⟨ refl ◈ (cong-∼ p ◈ refl) ⟩-∼

          ⟨ ϕ ⟩⁻¹ ◆ (mapOf (F ◆-𝐂𝐚𝐭 G) g ◆ ⟨ ϕ ⟩)

          ⟨ refl ◈ naturality g ⁻¹ ⟩-∼

          ⟨ ϕ ⟩⁻¹ ◆ (⟨ ϕ ⟩ ◆ g)

          ⟨ assoc-r-◆ ⟩-∼

          ⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩ ◆ g

          ⟨ inv-l-◆ (of ϕ) ◈ refl ⟩-∼

          id ◆ g

          ⟨ unit-l-◆ ⟩-∼

          g

          ∎

      instance
        isFaithful:F : isFaithful F
        isFaithful.isInjective:map isFaithful:F = record { cancel-injective = cancel-injective-F }

      module _ {a b : ⟨ 𝒟 ⟩} where
        cancel-injective-G : {f g : a ⟶ b} -> map f ∼ map g -> f ∼ g
        cancel-injective-G {f} {g} p =

          f

          ⟨ unit-l-◆ ⁻¹ ⟩-∼

          id ◆ f

          ⟨ inv-l-◆ (of ψ) ⁻¹ ◈ refl ⟩-∼

          ⟨ ψ ⟩⁻¹ ◆ ⟨ ψ ⟩ ◆ f

          ⟨ assoc-l-◆ ⟩-∼

          ⟨ ψ ⟩⁻¹ ◆ (⟨ ψ ⟩ ◆ f)

          ⟨ refl ◈ naturality f ⟩-∼

          ⟨ ψ ⟩⁻¹ ◆ (mapOf (G ◆-𝐂𝐚𝐭 F) f ◆ ⟨ ψ ⟩)

          ⟨ refl ◈ (cong-∼ p ◈ refl) ⟩-∼

          ⟨ ψ ⟩⁻¹ ◆ (mapOf (G ◆-𝐂𝐚𝐭 F) g ◆ ⟨ ψ ⟩)

          ⟨ refl ◈ naturality g ⁻¹ ⟩-∼

          ⟨ ψ ⟩⁻¹ ◆ (⟨ ψ ⟩ ◆ g)

          ⟨ assoc-r-◆ ⟩-∼

          ⟨ ψ ⟩⁻¹ ◆ ⟨ ψ ⟩ ◆ g

          ⟨ inv-l-◆ (of ψ) ◈ refl ⟩-∼

          id ◆ g

          ⟨ unit-l-◆ ⟩-∼

          g

          ∎

      instance
        isFaithful:G : isFaithful G
        isFaithful.isInjective:map isFaithful:G = record { cancel-injective = cancel-injective-G }

      --
      -- Next, we need to show that we have for the isomorphisms:
      -- |ϕ @ (FG X) ∼ FG (ϕ @ X)|
      --
      -- For that, we look at the following commuting square, given by naturality.
      -- $
      -- % https://q.uiver.app/?q=WzAsNCxbMCwwLCJYIl0sWzEsMCwiRkdYIl0sWzAsMSwiRkdYIl0sWzEsMSwiRkdGR1giXSxbMCwxLCJcXHBoaV57LTF9X1giXSxbMCwyLCJcXHBoaV57LTF9X1giLDJdLFsyLDMsIkZHXFxwaGleey0xfV9YIiwyXSxbMSwzLCJcXHBoaV57LTF9X3tGR1h9Il1d
      -- \[\begin{tikzcd}
      -- 	X & FGX \\
      -- 	FGX & FGFGX
      -- 	\arrow["{\phi^{-1}_X}", from=1-1, to=1-2]
      -- 	\arrow["{\phi^{-1}_X}"', from=1-1, to=2-1]
      -- 	\arrow["{FG\phi^{-1}_X}"', from=2-1, to=2-2]
      -- 	\arrow["{\phi^{-1}_{FGX}}", from=1-2, to=2-2]
      -- \end{tikzcd}\]
      -- $
      --
      -- It gives us the equation:
      prop-1 : ∀{x} -> ⟨ ϕ {⟨ G ⟩ (⟨ F ⟩ x)} ⟩⁻¹ ∼ mapOf (F ◆-𝐂𝐚𝐭 G) (⟨ ϕ {x} ⟩⁻¹)
      prop-1 {x} = ⟨ ϕ {⟨ G ⟩ (⟨ F ⟩ x)} ⟩⁻¹

               ⟨ unit-l-◆ ⁻¹ ⟩-∼

               id ◆ ⟨ ϕ {⟨ G ⟩ (⟨ F ⟩ x)} ⟩⁻¹

               ⟨ inv-r-◆ (of ϕ) ⁻¹ ◈ refl ⟩-∼

               ⟨ ϕ ⟩ ◆ ⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ {⟨ G ⟩ (⟨ F ⟩ x)} ⟩⁻¹

               ⟨ assoc-l-◆ ⟩-∼

               ⟨ ϕ ⟩ ◆ (⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ {⟨ G ⟩ (⟨ F ⟩ x)} ⟩⁻¹)

               ⟨ refl ◈ sym (naturality ⟨ ϕ ⟩⁻¹) ⟩-∼

               ⟨ ϕ ⟩ ◆ (⟨ ϕ ⟩⁻¹ ◆ mapOf (F ◆-𝐂𝐚𝐭 G) (⟨ ϕ {x} ⟩⁻¹))

               ⟨ assoc-r-◆ ⟩-∼

               (⟨ ϕ ⟩ ◆ ⟨ ϕ ⟩⁻¹) ◆ mapOf (F ◆-𝐂𝐚𝐭 G) (⟨ ϕ {x} ⟩⁻¹)

               ⟨ inv-r-◆ (of ϕ) ◈ refl ⟩-∼

               id ◆ mapOf (F ◆-𝐂𝐚𝐭 G) (⟨ ϕ {x} ⟩⁻¹)

               ⟨ unit-l-◆ ⟩-∼

               mapOf (F ◆-𝐂𝐚𝐭 G) (⟨ ϕ {x} ⟩⁻¹)

               ∎



      module _ {a b : ⟨ 𝒞 ⟩} where
        surj-F : ⟨ F ⟩ a ⟶ ⟨ F ⟩ b -> a ⟶ b
        surj-F f = ⟨ ϕ ⟩⁻¹ ◆ map f ◆ ⟨ ϕ ⟩

        instance
          isSetoidHom:surj-F : isSetoidHom (⟨ F ⟩ a ⟶ ⟨ F ⟩ b) (a ⟶ b) surj-F
          isSetoidHom:surj-F = record { cong-∼ = λ x → refl ◈ cong-∼ x ◈ refl }

        lem-1 : ∀{f} -> map (surj-F f) ∼ f
        lem-1 {f} = cancel-injective-G P
          where
            FG = F ◆-𝐂𝐚𝐭 G
            P : mapOf (F ◆-𝐂𝐚𝐭 G) (⟨ ϕ ⟩⁻¹ ◆ map f ◆ ⟨ ϕ ⟩) ∼ mapOf G f
            P = mapOf (F ◆-𝐂𝐚𝐭 G) (⟨ ϕ ⟩⁻¹ ◆ map f ◆ ⟨ ϕ ⟩)

                ⟨ functoriality-◆ {{of F ◆-𝐂𝐚𝐭 G}} ⟩-∼

                mapOf FG (⟨ ϕ ⟩⁻¹ ◆ map f) ◆ mapOf FG ⟨ ϕ ⟩

                ⟨ functoriality-◆ {{of F ◆-𝐂𝐚𝐭 G}} ◈ refl ⟩-∼

                mapOf FG ⟨ ϕ ⟩⁻¹ ◆ mapOf FG (map f) ◆ mapOf FG ⟨ ϕ ⟩

                ⟨ prop-1 ⁻¹ ◈ refl ◈ refl ⟩-∼

                ⟨ ϕ ⟩⁻¹ ◆ mapOf FG (map f) ◆ mapOf FG ⟨ ϕ ⟩

                ⟨ naturality (map f) ◈ refl ⟩-∼

                map f ◆ ⟨ ϕ ⟩⁻¹ ◆ mapOf FG ⟨ ϕ ⟩

                ⟨ refl ◈ prop-1 ◈ refl ⟩-∼

                map f ◆ mapOf FG ⟨ ϕ ⟩⁻¹ ◆ mapOf FG ⟨ ϕ ⟩

                ⟨ assoc-l-◆ ⟩-∼

                map f ◆ (mapOf FG ⟨ ϕ ⟩⁻¹ ◆ mapOf FG ⟨ ϕ ⟩)

                ⟨ refl ◈ functoriality-◆ {{of FG}} ⁻¹ ⟩-∼

                map f ◆ (mapOf FG (⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩))

                ⟨ refl ◈ cong-∼ (cong-∼ (inv-l-◆ (of ϕ))) ⟩-∼

                map f ◆ (mapOf FG id)

                ⟨ refl ◈ functoriality-id {{of FG}} ⟩-∼

                map f ◆ id

                ⟨ unit-r-◆ ⟩-∼

                map f

                ∎

        instance
          isSurjective:mapOfF : isSurjective (mapOf F {a = a} {b = b})
          isSurjective.surj isSurjective:mapOfF = surj-F
          isSurjective.isSetoidHom:surj isSurjective:mapOfF = it
          isSurjective.inv-surj isSurjective:mapOfF = lem-1

    isFull:byIsIso-𝐂𝐚𝐭 : isFull F
    isFull.isSurjective:map isFull:byIsIso-𝐂𝐚𝐭 = isSurjective:mapOfF

    isEssentiallySurjective:byIsIso-𝐂𝐚𝐭 : isEssentiallySurjective F
    isEssentiallySurjective.eso isEssentiallySurjective:byIsIso-𝐂𝐚𝐭 = ⟨ G ⟩
    isEssentiallySurjective.inv-eso isEssentiallySurjective:byIsIso-𝐂𝐚𝐭 = ψ


