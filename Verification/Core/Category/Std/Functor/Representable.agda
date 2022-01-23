
module Verification.Core.Category.Std.Functor.Representable where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid


record isIso-𝐒𝐭𝐝 {a : Setoid 𝑖} {b : Setoid 𝑗} (f : SetoidHom a b) : 𝒰 (𝑖 ､ 𝑗) where
  field inverse-𝐒𝐭𝐝 : SetoidHom b a
        inv-r-◆-𝐒𝐭𝐝 : (f ◆-𝐒𝐭𝐝 inverse-𝐒𝐭𝐝) ∼ id-𝐒𝐭𝐝
        inv-l-◆-𝐒𝐭𝐝 : (inverse-𝐒𝐭𝐝 ◆-𝐒𝐭𝐝 f) ∼ id-𝐒𝐭𝐝
open isIso-𝐒𝐭𝐝 {{...}} public

_≅-𝐒𝐭𝐝_ : (A : Setoid 𝑖) (B : Setoid 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
A ≅-𝐒𝐭𝐝 B = (SetoidHom A B) :& isIso-𝐒𝐭𝐝


-- module _ {𝒞 : 𝒰 _} {{_ : Category 𝑖 on 𝒞}} where
-- module _ {𝒞 : Category 𝑖} where
module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory 𝑖 𝒞}} where

  [_,_]-𝐒𝐭𝐝 : 𝒞 -> 𝒞 -> ⟨ 𝐒𝐭𝐝 _ ⟩
  [ x , y ]-𝐒𝐭𝐝 = ′ x ⟶ y ′

  [_,_]𝓈 = [_,_]-𝐒𝐭𝐝

[_,_]𝓊 = _⟶_
_≅𝓈_ = _≅-𝐒𝐭𝐝_


-- module _ {𝒞 : Category 𝑖} where
module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory 𝑖 𝒞}} where
  instance
    isSetoidHom:map[,] : ∀{a b c : 𝒞} -> {f : b ⟶ c} -> isSetoidHom [ a , b ]𝓈 [ a , c ]𝓈 (_◆ f)
    isSetoidHom:map[,] {f = f} =
      record {
        preserves-∼ = λ p -> p ◈ refl
      }

  instance
    isFunctor:Homᵒᵖ : ∀{x : 𝒞} -> isFunctor (′ 𝒞 ′) (𝐒𝐭𝐝 _) [ x ,_]-𝐒𝐭𝐝
    isFunctor.map isFunctor:Homᵒᵖ (f) = incl (′ (λ g -> g ◆ f) ′)
      -- where P : isSetoidHom _ _ (λ g -> g ◆ f)
      --       isSetoidHom.preserves-∼ P p = p ◈ refl
    isSetoidHom.preserves-∼ (isFunctor.isSetoidHom:map isFunctor:Homᵒᵖ) p = incl (incl (refl ◈ p))
    isFunctor.functoriality-id isFunctor:Homᵒᵖ = incl (incl (unit-r-◆))
    isFunctor.functoriality-◆ isFunctor:Homᵒᵖ = incl (incl assoc-r-◆)

  instance
    isSetoidHom:compose : ∀{a b c : 𝒞} -> {f : a ⟶ b} -> isSetoidHom [ b , c ]𝓈 [ a , c ]𝓈 (f ◆_)
    isSetoidHom:compose {f = f} = record { preserves-∼ = refl ◈_ }

  instance
    isFunctor:Hom : ∀{y : 𝒞} -> isFunctor (′ 𝒞 ′ ᵒᵖ) (𝐒𝐭𝐝 _) [_, y ]-𝐒𝐭𝐝
    isFunctor.map isFunctor:Hom (incl f) = incl ′(incl f ◆_)′
    isSetoidHom.preserves-∼ (isFunctor.isSetoidHom:map isFunctor:Hom) (incl p) = incl (incl (incl p ◈ refl))
    isFunctor.functoriality-id isFunctor:Hom = incl (incl (unit-l-◆))
    isFunctor.functoriality-◆ isFunctor:Hom = incl (incl assoc-l-◆)

module _ {𝒞 : Category 𝑖} where
  record isCorep (F : Functor 𝒞 (𝐒𝐭𝐝 _)) (x : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ⁺) where
    field corep : F ≅ ′ [ x ,_]𝓈 ′

  open isCorep {{...}} public
  Corep : (Functor 𝒞 (𝐒𝐭𝐝 _)) -> 𝒰 _
  Corep F = Structure (isCorep F)

module _ {𝒞 : Category 𝑖} where
  module _ {F : Functor (𝒞) (𝐒𝐭𝐝 _)} {x : ⟨ 𝒞 ⟩} where

    よᵒᵖ : [ ′ [ x ,_]𝓈 ′ , F ]𝓈 ≅𝓈 (⟨ F ⟩ x)
    よᵒᵖ = ′ f ′ {{P₁}}
      where f : (′ [ x ,_]-𝐒𝐭𝐝 ′) ⟶ F -> ⟨ (⟨ F ⟩ x) ⟩
            f α = let α' = ⟨ ⟨ ⟨ ⟨ α ⟩ ⟩ {x} ⟩ ⟩
                  in α' id

            g : ⟨ ⟨ F ⟩ x ⟩  ->  [ ′ [ x ,_]𝓈 ′ , F ]𝓊
            g a = let α : ∀{y} -> [ x , y ]𝓊  -> ⟨ ⟨ F ⟩ y ⟩
                      α f = ⟨ ⟨ map f ⟩ ⟩ a

                      instance
                        P₀ : ∀{y} -> isSetoidHom [ x , y ]𝓈 (⟨ F ⟩ y) (α {y})
                        P₀ {y} = record {
                          preserves-∼ = λ {f} {g} f∼g ->
                            let P₁ : map {{of F}} f ∼ map {{of F}} g
                                P₁ = preserves-∼ f∼g
                            in ⟨ ⟨ P₁ ⟩ ⟩ {a}
                          }

                        P₁ : isNatural ′ [ x ,_]𝓈 ′ F (incl ′ α ′)
                        P₁ = record {
                          naturality = λ f -> incl (incl (λ {g} ->
                            let instance
                                  P₂ : ∀{y} -> isSetoid _ ⟨ ⟨ F ⟩ y ⟩
                                  P₂ {y} = of (⟨ F ⟩ y)
                                P₃ : ⟨ ⟨ map {{of F}} f ⟩ ⟩ (⟨ ⟨ map {{of F}} g ⟩ ⟩ a) ∼ ⟨ ⟨ map {{of F}} (g ◆ f) ⟩ ⟩ a
                                P₃ = ⟨ ⟨ functoriality-◆ {{of F}} ⁻¹ ⟩ ⟩
                            in P₃
                            ))
                          }
                  in incl ′ (incl ′ α ′) ′

            instance
              P₀ : isSetoidHom (′ (′ [ x ,_]-𝐒𝐭𝐝 ′) ⟶ F ′) (⟨ F ⟩ x) f
              isSetoidHom.preserves-∼ P₀ {a = a} {b} (incl p) = ⟨ ⟨ p {x} ⟩ ⟩ {id}

              P₂ : isSetoidHom _ _ g
              isSetoidHom.preserves-∼ P₂ (p) = incl (incl (incl (λ {f} -> preserves-∼ {{of ⟨ map {{of F}} f ⟩}} p)))
            P₁ : isIso-𝐒𝐭𝐝 ′ f ′
            isIso-𝐒𝐭𝐝.inverse-𝐒𝐭𝐝 P₁ = ′ g ′
            isIso-𝐒𝐭𝐝.inv-r-◆-𝐒𝐭𝐝 P₁ = incl (λ {α} -> incl (λ {x} -> incl (incl (λ {f} ->
                let P₄ : ⟨ ⟨ α ⟩ ⟩ ◆ map {{of F}} f ∼ incl ′(_◆ f)′ ◆ ⟨ ⟨ α ⟩ ⟩
                    P₄ = naturality {{of ⟨ α ⟩}} f
                    P₅ = ⟨ ⟨ P₄ ⟩ ⟩ {id}

                    instance
                      P₆ : isSetoid _ ⟨ ⟨ F ⟩ x ⟩
                      P₆ = of (⟨ F ⟩ x)

                    instance
                      P₈ = isEquivRel:∼ {{P₆}}

                    P₇ : ⟨ ⟨ ⟨ ⟨ α ⟩ ⟩ ⟩ ⟩ (id ◆ f) ∼ ⟨ ⟨ ⟨ ⟨ α ⟩ ⟩ ⟩ ⟩ f
                    P₇ = preserves-∼ {{of ⟨ ⟨ ⟨ α ⟩ ⟩ ⟩}} unit-l-◆

                in P₅ ∙ P₇
              )) ))
            isIso-𝐒𝐭𝐝.inv-l-◆-𝐒𝐭𝐝 P₁ = incl (λ {a} -> ⟨ ⟨ functoriality-id ⟩ ⟩)



-- {{isSetoidHom:map[,] {𝒞 = ⟨ 𝒞 ⟩}}}
{-
--   instance
--     isFunctor:Hom : ∀{y : ⟨ 𝒞 ⟩} -> isFunctor (𝒞 ᵒᵖ) (𝐒𝐭𝐝 _) [_, y ]-𝐒𝐭𝐝
--     isFunctor.map isFunctor:Hom (incl f) = incl (′ (λ g -> incl f ◆ g) ′ {{P}})
--       where P : isSetoidHom (λ g -> incl f ◆ g)
--             isSetoidHom.preserves-∼ P p = incl ⟨ refl {{isEquivRel:∼ {{isSetoid:Hom {{of 𝒞}}}}}} ⟩ ◈ p
--             -- incl ⟨ (refl) {{of 𝒞 ᵒᵖ}} ⟩ ◈ p
--     isSetoidHom.preserves-∼ (isFunctor.isSetoidHom:map isFunctor:Hom) (incl p) = incl (incl (λ {a₂} -> incl (sym p) ◈ ?))
--     isFunctor.functoriality-id isFunctor:Hom = {!!}
--     isFunctor.functoriality-◆ isFunctor:Hom = {!!}

--   record isRepresentable (F : Functor (𝒞 ᵒᵖ) (𝐒𝐭𝐝 _)) : 𝒰 (𝑖 ⁺) where
--     field Repr : ⟨ 𝒞 ⟩
--     field repr : F ≅ ′ [_, Repr ]-𝐒𝐭𝐝 ′

-- module _ {𝒞 : Category 𝑖} where
--   module _ {F : Functor (𝒞 ᵒᵖ) (𝐒𝐭𝐝 _)} {x : ⟨ 𝒞 ⟩} where
--     X : Functor (𝒞 ᵒᵖ) (𝐒𝐭𝐝 _)
--     X = ′ [_, x ]-𝐒𝐭𝐝 ′ {{isFunctor:Hom {𝒞 = 𝒞} {y = x}}}

    -- よ : ′ (′ [_, x ]-𝐒𝐭𝐝 ′ {{isFunctor:Hom}}) ⟶ F ′ ≅-𝐒𝐭𝐝 (⟨ F ⟩ x)
    -- よ = {!!}



-}


