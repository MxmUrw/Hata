
module Verification.Experimental.Category.Std.Functor.Representable where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid


record isIso-Std {a : Setoid 𝑖} {b : Setoid 𝑗} (f : SetoidHom a b) : 𝒰 (𝑖 ､ 𝑗) where
  field inverse-Std : SetoidHom b a
        inv-r-◆-Std : (f ◆-Std inverse-Std) ∼ id-Std
        inv-l-◆-Std : (inverse-Std ◆-Std f) ∼ id-Std
open isIso-Std {{...}} public

_≅-Std_ : (A : Setoid 𝑖) (B : Setoid 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
A ≅-Std B = (SetoidHom A B) :& isIso-Std


-- module _ {𝒞 : 𝒰 _} {{_ : Category 𝑖 on 𝒞}} where
-- module _ {𝒞 : Category 𝑖} where
module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory 𝑖 𝒞}} where

  [_,_]-Std : 𝒞 -> 𝒞 -> ⟨ Std _ ⟩
  [ x , y ]-Std = ′ x ⟶ y ′

  [_,_]𝓈 = [_,_]-Std

[_,_]𝓊 = _⟶_
_≅𝓈_ = _≅-Std_


-- module _ {𝒞 : Category 𝑖} where
module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory 𝑖 𝒞}} where
  instance
    isSetoidHom:map[,] : ∀{a b c : 𝒞} -> {f : b ⟶ c} -> isSetoidHom [ a , b ]𝓈 [ a , c ]𝓈 (_◆ f)
    isSetoidHom:map[,] {f = f} =
      record {
        preserves-∼ = λ p -> p ◈ refl
      }

  instance
    isFunctor:Homᵒᵖ : ∀{x : 𝒞} -> isFunctor (′ 𝒞 ′) (Std _) [ x ,_]-Std
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
    isFunctor:Hom : ∀{y : 𝒞} -> isFunctor (′ 𝒞 ′ ᵒᵖ) (Std _) [_, y ]-Std
    isFunctor.map isFunctor:Hom (incl f) = incl ′(incl f ◆_)′
    isSetoidHom.preserves-∼ (isFunctor.isSetoidHom:map isFunctor:Hom) (incl p) = incl (incl (incl p ◈ refl))
    isFunctor.functoriality-id isFunctor:Hom = incl (incl (unit-l-◆))
    isFunctor.functoriality-◆ isFunctor:Hom = incl (incl assoc-l-◆)

module _ {𝒞 : Category 𝑖} where
  record isCorep (F : Functor 𝒞 (Std _)) (x : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ⁺) where
    field corep : F ≅ ′ [ x ,_]𝓈 ′

  open isCorep {{...}} public
  Corep : (Functor 𝒞 (Std _)) -> 𝒰 _
  Corep F = Structure (isCorep F)

module _ {𝒞 : Category 𝑖} where
  module _ {F : Functor (𝒞) (Std _)} {x : ⟨ 𝒞 ⟩} where

    よᵒᵖ : [ ′ [ x ,_]𝓈 ′ , F ]𝓈 ≅𝓈 (⟨ F ⟩ x)
    よᵒᵖ = ′ f ′ {{P₁}}
      where f : (′ [ x ,_]-Std ′) ⟶ F -> ⟨ (⟨ F ⟩ x) ⟩
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
              P₀ : isSetoidHom (′ (′ [ x ,_]-Std ′) ⟶ F ′) (⟨ F ⟩ x) f
              isSetoidHom.preserves-∼ P₀ {a = a} {b} (incl p) = ⟨ ⟨ p {x} ⟩ ⟩ {id}

              P₂ : isSetoidHom _ _ g
              isSetoidHom.preserves-∼ P₂ (p) = incl (incl (incl (λ {f} -> preserves-∼ {{of ⟨ map {{of F}} f ⟩}} p)))
            P₁ : isIso-Std ′ f ′
            isIso-Std.inverse-Std P₁ = ′ g ′
            isIso-Std.inv-r-◆-Std P₁ = incl (λ {α} -> incl (λ {x} -> incl (incl (λ {f} ->
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
            isIso-Std.inv-l-◆-Std P₁ = incl (λ {a} -> ⟨ ⟨ functoriality-id ⟩ ⟩)



-- {{isSetoidHom:map[,] {𝒞 = ⟨ 𝒞 ⟩}}}
{-
--   instance
--     isFunctor:Hom : ∀{y : ⟨ 𝒞 ⟩} -> isFunctor (𝒞 ᵒᵖ) (Std _) [_, y ]-Std
--     isFunctor.map isFunctor:Hom (incl f) = incl (′ (λ g -> incl f ◆ g) ′ {{P}})
--       where P : isSetoidHom (λ g -> incl f ◆ g)
--             isSetoidHom.preserves-∼ P p = incl ⟨ refl {{isEquivRel:∼ {{isSetoid:Hom {{of 𝒞}}}}}} ⟩ ◈ p
--             -- incl ⟨ (refl) {{of 𝒞 ᵒᵖ}} ⟩ ◈ p
--     isSetoidHom.preserves-∼ (isFunctor.isSetoidHom:map isFunctor:Hom) (incl p) = incl (incl (λ {a₂} -> incl (sym p) ◈ ?))
--     isFunctor.functoriality-id isFunctor:Hom = {!!}
--     isFunctor.functoriality-◆ isFunctor:Hom = {!!}

--   record isRepresentable (F : Functor (𝒞 ᵒᵖ) (Std _)) : 𝒰 (𝑖 ⁺) where
--     field Repr : ⟨ 𝒞 ⟩
--     field repr : F ≅ ′ [_, Repr ]-Std ′

-- module _ {𝒞 : Category 𝑖} where
--   module _ {F : Functor (𝒞 ᵒᵖ) (Std _)} {x : ⟨ 𝒞 ⟩} where
--     X : Functor (𝒞 ᵒᵖ) (Std _)
--     X = ′ [_, x ]-Std ′ {{isFunctor:Hom {𝒞 = 𝒞} {y = x}}}

    -- よ : ′ (′ [_, x ]-Std ′ {{isFunctor:Hom}}) ⟶ F ′ ≅-Std (⟨ F ⟩ x)
    -- よ = {!!}



-}


