
module Verification.Core.Category.Std.Functor.Equivalence where

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


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isIso-𝐂𝐚𝐭 (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field inverse-◆-𝐂𝐚𝐭 : Functor 𝒟 𝒞
    field inv-r-◆-𝐂𝐚𝐭 : F ◆-𝐂𝐚𝐭 inverse-◆-𝐂𝐚𝐭 ∼ id
    field inv-l-◆-𝐂𝐚𝐭 : inverse-◆-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F ∼ id

  open isIso-𝐂𝐚𝐭 public

  module _ {F : Functor 𝒞 𝒟} {{_ : isFull F}} {{_ : isFaithful F}} {{EsoP : isEssentiallySurjective F}} where
    private
      map-eso : ∀{a b : ⟨ 𝒟 ⟩} -> a ⟶ b -> eso a ⟶ eso b
      map-eso {a} {b} f =
        let f' : ⟨ F ⟩ (eso a) ⟶ ⟨ F ⟩ (eso b)
            f' = ⟨ inv-eso ⟩ ◆ f ◆ ⟨ inv-eso ⟩⁻¹
        in surj f'

      lem-0 : ∀{a b : ⟨ 𝒟 ⟩} -> {f g : a ⟶ b} -> (f ∼ g) -> map-eso f ∼ map-eso g
      lem-0 p = cong-∼ {{isSetoidHom:surj}} ((refl ◈ p ◈ refl))

      lem-1 : ∀{a b : ⟨ 𝒟 ⟩} -> isSetoidHom (a ⟶ b) (eso a ⟶ eso b) map-eso
      lem-1 {a} {b} = record { cong-∼ = lem-0 }

      lem-2 : ∀{a : ⟨ 𝒟 ⟩} -> map-eso (id {a = a}) ∼ id
      lem-2 = cancel-injective lem-2a
        where
          lem-2a : ∀{a : ⟨ 𝒟 ⟩} -> mapOf F (map-eso (id {a = a})) ∼ mapOf F id
          lem-2a {a} =
            mapOf F (surj (⟨ inv-eso ⟩ ◆ (id {a = a}) ◆ ⟨ inv-eso ⟩⁻¹))
            ⟨ inv-surj ⟩-∼
            ⟨ inv-eso ⟩ ◆ (id {a = a}) ◆ ⟨ inv-eso ⟩⁻¹
            ⟨ unit-r-◆ ◈ refl ⟩-∼
            ⟨ inv-eso ⟩ ◆ ⟨ inv-eso ⟩⁻¹
            ⟨ inv-r-◆ (of inv-eso) ⟩-∼
            id {a = ⟨ F ⟩ (eso a)}
            ⟨ functoriality-id ⁻¹ ⟩-∼
            mapOf F id
            ∎

      lem-3 : ∀{a b c : ⟨ 𝒟 ⟩} -> {f : a ⟶ b} {g : b ⟶ c} -> map-eso (f ◆ g) ∼ map-eso f ◆ map-eso g
      lem-3 {a} {b} {c} {f} {g} = cancel-injective lem-3a
        where
          lem-3a : mapOf F (map-eso (f ◆ g)) ∼ mapOf F (map-eso f ◆ map-eso g)
          lem-3a = map (surj (⟨ inv-eso ⟩ ◆ (f ◆ g) ◆ ⟨ inv-eso ⟩⁻¹))

                      ⟨ inv-surj ⟩-∼

                    (⟨ inv-eso ⟩ ◆ (f ◆ g) ◆ ⟨ inv-eso ⟩⁻¹)

                      ⟨ assoc-[ab][cd]∼a[bc]d-◆ ⁻¹ ⟩-∼

                    ⟨ inv-eso ⟩ ◆ f ◆ (g ◆ ⟨ inv-eso ⟩⁻¹)

                      ⟨ refl ◈ refl ◈ unit-l-◆ ⁻¹ ⟩-∼

                    ⟨ inv-eso ⟩ ◆ f ◆ (id ◆ (g ◆ ⟨ inv-eso ⟩⁻¹))

                      ⟨ refl ◈ refl ◈ (inv-l-◆ (of inv-eso) ⁻¹  ◈ refl) ⟩-∼

                    ⟨ inv-eso ⟩ ◆ f ◆ ((⟨ inv-eso ⟩⁻¹ ◆ ⟨ inv-eso ⟩) ◆ (g ◆ ⟨ inv-eso ⟩⁻¹))

                      ⟨ refl ◈ refl ◈ (assoc-l-◆) ⟩-∼

                    ⟨ inv-eso ⟩ ◆ f ◆ (⟨ inv-eso ⟩⁻¹ ◆ (⟨ inv-eso ⟩ ◆ (g ◆ ⟨ inv-eso ⟩⁻¹)))

                      ⟨ refl ◈ refl ◈ (refl ◈ (assoc-r-◆)) ⟩-∼

                    ⟨ inv-eso ⟩ ◆ f ◆ (⟨ inv-eso ⟩⁻¹ ◆ (⟨ inv-eso ⟩ ◆ g ◆ ⟨ inv-eso ⟩⁻¹))

                      ⟨ assoc-r-◆ ⟩-∼

                    (⟨ inv-eso ⟩ ◆ f ◆ ⟨ inv-eso ⟩⁻¹) ◆ (⟨ inv-eso ⟩ ◆ g ◆ ⟨ inv-eso ⟩⁻¹)

                      ⟨ inv-surj ⁻¹ ◈ inv-surj ⁻¹ ⟩-∼

                    map (surj (⟨ inv-eso ⟩ ◆ f ◆ ⟨ inv-eso ⟩⁻¹)) ◆ map (surj (⟨ inv-eso ⟩ ◆ g ◆ ⟨ inv-eso ⟩⁻¹))

                      ⟨ functoriality-◆ ⁻¹ ⟩-∼

                    map ((surj (⟨ inv-eso ⟩ ◆ f ◆ ⟨ inv-eso ⟩⁻¹)) ◆ surj (⟨ inv-eso ⟩ ◆ g ◆ ⟨ inv-eso ⟩⁻¹))

                      ∎


      instance
        lem-5 : isFunctor 𝒟 𝒞 eso
        isFunctor.map lem-5 = map-eso
        isFunctor.isSetoidHom:map lem-5 = lem-1
        isFunctor.functoriality-id lem-5 = lem-2
        isFunctor.functoriality-◆ lem-5 = lem-3

      lem-6 : F ◆-𝐂𝐚𝐭 ′ eso ′ ∼ id
      lem-6 = α since Proof
        where

          ψ : ∀{x} -> ⟨ F ⟩ (eso (⟨ F ⟩ x)) ≅ ⟨ F ⟩ x
          ψ = inv-eso

          ϕ : ∀{x} -> eso (⟨ F ⟩ x) ≅ x
          ϕ = cong⁻¹-≅ ψ

          α : Natural (F ◆-𝐂𝐚𝐭 ′ eso ′) id
          α = (λ x -> ⟨ ϕ ⟩) since natural λ f -> cancel-injective (P f)
            where
              P : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> map (⟨ ϕ ⟩ ◆ f) ∼ map (mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f ◆ ⟨ ϕ ⟩)
              P f = map (⟨ ϕ ⟩ ◆ f)

                    ⟨ functoriality-◆ ⟩-∼

                  map ⟨ ϕ ⟩ ◆ map f

                    ⟨ inv-surj ◈ refl ⟩-∼

                  ⟨ ψ ⟩ ◆ map f

                    ⟨ unit-r-◆ ⁻¹ ⟩-∼

                  ⟨ ψ ⟩ ◆ map f ◆ id

                    ⟨ refl ◈ inv-l-◆ (of ψ) ⁻¹ ⟩-∼

                  ⟨ ψ ⟩ ◆ map f ◆ (⟨ ψ ⟩⁻¹ ◆ ⟨ ψ ⟩)

                    ⟨ assoc-r-◆ ⟩-∼

                  (⟨ ψ ⟩ ◆ map f ◆ ⟨ ψ ⟩⁻¹) ◆ ⟨ ψ ⟩

                    ⟨ inv-surj ⁻¹ ◈ refl ⟩-∼

                  map (mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f) ◆ ⟨ ψ ⟩

                    ⟨ refl ◈ inv-surj ⁻¹ ⟩-∼

                  map (mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f) ◆ map ⟨ ϕ ⟩

                    ⟨ functoriality-◆ ⁻¹ ⟩-∼

                  map (mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f ◆ ⟨ ϕ ⟩)

                    ∎

          β : Natural id (F ◆-𝐂𝐚𝐭 ′ eso ′)
          β = (λ x -> ⟨ ϕ ⟩⁻¹) since natural λ f -> cancel-injective (P f)
            where
              P : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> map (⟨ ϕ ⟩⁻¹ ◆ mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f) ∼ map (f ◆ ⟨ ϕ ⟩⁻¹)
              P f = map (⟨ ϕ ⟩⁻¹ ◆ mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f)

                    ⟨ functoriality-◆ ⟩-∼

                    map ⟨ ϕ ⟩⁻¹ ◆ map (mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f)

                    ⟨ inv-surj ◈ refl ⟩-∼

                    ⟨ ψ ⟩⁻¹ ◆ map (mapOf (F ◆-𝐂𝐚𝐭 ′ eso ′) f)

                    ⟨ refl ◈ inv-surj ⟩-∼

                    ⟨ ψ ⟩⁻¹ ◆ (⟨ ψ ⟩ ◆ map f ◆ ⟨ ψ ⟩⁻¹)

                    ⟨ (refl ◈ assoc-l-◆) ∙ assoc-r-◆ ⟩-∼

                    (⟨ ψ ⟩⁻¹ ◆ ⟨ ψ ⟩) ◆ (map f ◆ ⟨ ψ ⟩⁻¹)

                    ⟨ inv-l-◆ (of ψ) ◈ refl ⟩-∼

                    id ◆ (map f ◆ ⟨ ψ ⟩⁻¹)

                    ⟨ unit-l-◆ ⟩-∼

                    (map f ◆ ⟨ ψ ⟩⁻¹)

                    ⟨ refl ◈ inv-surj ⁻¹ ⟩-∼

                    (map f ◆ map ⟨ ϕ ⟩⁻¹)

                    ⟨ functoriality-◆ ⁻¹ ⟩-∼

                    (map (f ◆ ⟨ ϕ ⟩⁻¹))

                    ∎

          Proof : isIso (hom α)
          Proof = record
            { inverse-◆ = β
            ; inv-r-◆ = componentwise (λ x → inv-r-◆ (of ϕ))
            ; inv-l-◆ = componentwise (λ x → inv-l-◆ (of ϕ))
            }


      lem-7 : ′ eso ′ ◆-𝐂𝐚𝐭 F ∼ id
      lem-7 = α since Proof
        where
          ψ = inv-eso

          --
          -- Note: the naturality proof is almost the same as above
          --
          α : Natural (′ eso ′ ◆-𝐂𝐚𝐭 F) id
          α = (λ x → ⟨ inv-eso ⟩) since natural (λ f → P f)
            where
              P : ∀{a b : ⟨ 𝒟 ⟩} -> (f : a ⟶ b) -> (⟨ ψ ⟩ ◆ f) ∼ (mapOf (′ eso ′ ◆-𝐂𝐚𝐭 F) f ◆ ⟨ ψ ⟩)
              P f = ⟨ ψ ⟩ ◆ f

                    ⟨ unit-r-◆ ⁻¹ ⟩-∼

                  ⟨ ψ ⟩ ◆ f ◆ id

                    ⟨ refl ◈ inv-l-◆ (of ψ) ⁻¹ ⟩-∼

                  ⟨ ψ ⟩ ◆ f ◆ (⟨ ψ ⟩⁻¹ ◆ ⟨ ψ ⟩)

                    ⟨ assoc-r-◆ ⟩-∼

                  (⟨ ψ ⟩ ◆ f ◆ ⟨ ψ ⟩⁻¹) ◆ ⟨ ψ ⟩

                    ⟨ inv-surj ⁻¹ ◈ refl ⟩-∼

                  (mapOf (′ eso ′ ◆-𝐂𝐚𝐭 F) f) ◆ ⟨ ψ ⟩

                    ∎

          β : Natural id (′ eso ′ ◆-𝐂𝐚𝐭 F)
          β = (λ x → ⟨ inv-eso ⟩⁻¹) since natural λ f → P f
            where
              P : ∀{a b : ⟨ 𝒟 ⟩} -> (f : a ⟶ b) -> (⟨ ψ ⟩⁻¹ ◆ mapOf (′ eso ′ ◆-𝐂𝐚𝐭 F) f) ∼ (f ◆ ⟨ ψ ⟩⁻¹)
              P f = ⟨ ψ ⟩⁻¹ ◆ mapOf (′ eso ′ ◆-𝐂𝐚𝐭 F) f

                    ⟨ refl ◈ inv-surj ⟩-∼

                    ⟨ ψ ⟩⁻¹ ◆ (⟨ ψ ⟩ ◆ f ◆ ⟨ ψ ⟩⁻¹)

                    ⟨ (refl ◈ assoc-l-◆) ∙ assoc-r-◆ ⟩-∼

                    (⟨ ψ ⟩⁻¹ ◆ ⟨ ψ ⟩) ◆ (f ◆ ⟨ ψ ⟩⁻¹)

                    ⟨ inv-l-◆ (of ψ) ◈ refl ⟩-∼

                    id ◆ (f ◆ ⟨ ψ ⟩⁻¹)

                    ⟨ unit-l-◆ ⟩-∼

                    f ◆ ⟨ ψ ⟩⁻¹

                    ∎

          Proof : isIso (hom α)
          Proof = record
            { inverse-◆ = β
            ; inv-r-◆ = componentwise (λ x → inv-r-◆ (of inv-eso))
            ; inv-l-◆ = componentwise (λ x → inv-l-◆ (of inv-eso))
            }

    isIso-𝐂𝐚𝐭:byFFEso : isIso-𝐂𝐚𝐭 F
    isIso-𝐂𝐚𝐭:byFFEso = Proof
      where
        Proof = record
          { inverse-◆-𝐂𝐚𝐭 = eso since lem-5
          ; inv-r-◆-𝐂𝐚𝐭 = lem-6
          ; inv-l-◆-𝐂𝐚𝐭 = lem-7
          }

module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where
  _≅-𝐂𝐚𝐭_ = (Functor 𝒞 𝒟) :& isIso-𝐂𝐚𝐭

pattern _since_andAlso_ a b c = ′_′ a {make∑i {{b}}} {{c}}

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  sym-≅-𝐂𝐚𝐭 : 𝒞 ≅-𝐂𝐚𝐭 𝒟 -> 𝒟 ≅-𝐂𝐚𝐭 𝒞
  sym-≅-𝐂𝐚𝐭 p = ⟨ inverse-◆-𝐂𝐚𝐭 (of p) ⟩ since of inverse-◆-𝐂𝐚𝐭 (of p) andAlso record
    { inverse-◆-𝐂𝐚𝐭 = ⟨ p ⟩ since it
    ; inv-r-◆-𝐂𝐚𝐭 = inv-l-◆-𝐂𝐚𝐭 (of p)
    ; inv-l-◆-𝐂𝐚𝐭 = inv-r-◆-𝐂𝐚𝐭 (of p)
    }


