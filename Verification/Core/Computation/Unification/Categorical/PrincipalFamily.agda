
module Verification.Core.Computation.Unification.Categorical.PrincipalFamily where

open import Verification.Conventions
open import Verification.Core.Set.Induction.WellFounded
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Computation.Unification.Categorical.Definition


record hasSizedFamily (𝑗 : 𝔏) (𝒞 : ZeroMorphismCategory 𝑖) : 𝒰 (𝑗 ⁺ ､ 𝑖 ⁺) where
  field Base : ⟨ 𝒞 ⟩ -> 𝒰 𝑗
  field Ind : ⟨ 𝒞 ⟩ -> 𝒰 𝑗
  field 𝒷 : ∀ {a} -> Base a -> Ind a
  field 𝓘 : ∀ {a} -> (i : Ind a) -> Ideal a
  field Size : WFT (ℓ₀ , ℓ₀)
  field size : ∀{a} -> Ind a -> ⟨ Size ⟩

open hasSizedFamily {{...}} public

module _ (𝑗 : 𝔏 ^ 4) where
  CategoryWithSizedFamily : _
  CategoryWithSizedFamily = (ZeroMorphismCategory (𝑗 ⌄ 0 ⋯ 2)) :& hasSizedFamily (𝑗 ⌄ 3)



module _ {𝑖 : 𝔏 ^ 3} {𝒞 : Category 𝑖} {{_ : isZeroMorphismCategory 𝒞}} {{_ : isSizedCategory 𝒞}} where

  module _ {{_ : hasSizedFamily 𝑗 ′ ⟨ 𝒞 ⟩ ′}} where
    record isSplittable {a : ⟨ 𝒞 ⟩} (n : ℕ) (i : Ind a) : 𝒰 (𝑗 ､ 𝑖 ⁺) where
      field fam : Fin-R n -> Ind a
      field covers : ⋀-fin (λ i -> 𝓘 (fam i)) ∼ 𝓘 i
      field famprops : ∀ k -> size (fam k) ≪ size i
    open isSplittable public

record hasPrincipalFamily {𝑖 : 𝔏 ^ 3} {𝑗 : 𝔏} (𝒞 : Category 𝑖 :& (isSizedCategory :, (isZeroMorphismCategory :> hasSizedFamily 𝑗))) : 𝒰 (𝑖 ⁺ ､ 𝑗) where
  field _⁻¹*_ : ∀{a b : ⟨ 𝒞 ⟩} (f : a ⟶ b) -> Ind a -> Ind b
  field size:⁻¹* : ∀{a b : ⟨ 𝒞 ⟩} (g : a ⟶ b) -> isGood g -> (i : Ind a) -> size (g ⁻¹* i) ⪣ size i
  field preserves-𝓘:⁻¹* : ∀{a b : ⟨ 𝒞 ⟩} {g : a ⟶ b} -> {i : Ind a} -> 𝓘 (g ⁻¹* i) ∼ (g ⁻¹↷ (𝓘 i))
  field principalBase : ∀ {a : ⟨ 𝒞 ⟩} -> ∀ (b : Base a) -> isEpiPrincipal (𝓘 (𝒷 b))
  field ∂ : ∀{a : ⟨ 𝒞 ⟩}(i : Ind a) -> (∑ λ (b : Base a) -> 𝓘 (𝒷 b) ∼ 𝓘 i) +-𝒰 (∑ λ n -> isSplittable n i)

open hasPrincipalFamily {{...}} public

module _ (𝑗 : 𝔏 ^ 4) where
  CategoryWithPrincipalFamily : _
  CategoryWithPrincipalFamily = _ :& hasPrincipalFamily {𝑗 ⌄ (0 ⋯ 2)} {𝑗 ⌄ 3}

module _ (𝒞 : 𝒰 𝑖)
  {{_ : isCategory {𝑗} 𝒞 }}
  {{_ : isSizedCategory ′ 𝒞 ′}}
  {{_ : isZeroMorphismCategory ′ 𝒞 ′}}
  {{_ : hasSizedFamily 𝑘 ′ 𝒞 ′}}
  {{_ : hasPrincipalFamily ′ 𝒞 ′}}
  -- {{_ : CategoryWithPrincipalFamily 𝑖 on 𝒞}} where
  where

  private
    P : (s : ⟨ Size ⟩) -> 𝒰 _
    P s = ∀{a : 𝒞} -> ∀ (i : Ind a) -> size i ≡-Str s -> isEpiPrincipal (𝓘 i)

    lem-40 : ∀{a : 𝒞} {U V : Ideal a}
              -> (PU : isEpiPrincipal U)
              -> isEpiPrincipal (repOf U {{PU}} ⁻¹↷ V)
              -> isEpiPrincipal (V ∧ U)
    lem-40 {a} {U} {V} PU PV =
      let
          instance _ = PU
          instance _ = PV

          u : a ⟶ repObjOf U
          u = repOf U

          V' = u ⁻¹↷ V

          v : repObjOf U ⟶ repObjOf V'
          v = repOf V'

          P₈ : (V ∧ U) ∼ (u ◆ v) ↷ ⊤-Ideal
          P₈ = V ∧ U                                          ⟨ refl ≀∧≀ principal-r ⟩-∼
                (V ∧ (u ↷ ⊤-Ideal))                                 ⟨ inv-↷-r ⁻¹ ⟩-∼
                (u ↷ ((u ⁻¹↷ V)))                              ⟨ refl ≀↷≀ (principal-r)  ⟩-∼
                (u ↷ ((v ↷ ⊤-Ideal)))                                ⟨ assoc-l-↷ ⁻¹ ⟩-∼
                ((u ◆ v) ↷ ⊤-Ideal)                                   ∎

      in record
         { repObj = _
         ; rep = u ◆ v
         ; principal-r = P₈
         ; isGoodRep = isGood:◆ isGoodRep isGoodRep
         ; zeroOrEpi = isZeroOrEpi:◆ {𝒞' = ′ 𝒞 ′} zeroOrEpi zeroOrEpi
         }


    lem-45 : ∀{n} {a : 𝒞} -> (F : Fin-R n -> Ind a)
             -> (∀ (i) -> ∀{b} -> ∀ (g : a ⟶ b) -> isGood g -> isEpiPrincipal (𝓘 (g ⁻¹* F i)))
             -> isEpiPrincipal (⋀-fin (λ j -> 𝓘 (F j)))
    lem-45 {zero} {a} F FP = isEpiPrincipal:⊤
    lem-45 {suc n} {a} F FP =
        let
            instance
              P₀ : isEpiPrincipal (⋀-fin (λ j -> 𝓘 (F (suc j))))
              P₀ = (lem-45 (λ j -> F (suc j)) (λ j -> FP (suc j)))

            r : a ⟶ _
            r = repOf (⋀-fin (λ j -> 𝓘 (F (suc j)))) {{P₀}}

            P₁ : isEpiPrincipal (𝓘 (r ⁻¹* F zero))
            P₁ = FP zero r (isGoodRep {{_}} {{P₀}})

            P₂ : isEpiPrincipal (r ⁻¹↷ 𝓘 (F zero))
            P₂ = transp-isEpiPrincipal preserves-𝓘:⁻¹* P₁
        in lem-40 P₀ P₂

    lem-50 : ∀ s -> (∀ t -> t ≪ s -> P t) -> P s
    lem-50 s IH {a} k refl-StrId with ∂ k
    ... | left (b , P) = let P₀ = principalBase b
                         in transp-isEpiPrincipal P P₀
    ... | just (n , Split) =
      let P₀ : ∀(i) -> ∀{b : 𝒞} -> ∀(g : a ⟶ b) -> isGood g -> isEpiPrincipal (𝓘 (g ⁻¹* Split .fam i))
          P₀ i g good = case size:⁻¹* g good (fam Split i) of
                      (λ p ->
                        let Q₀ : size (fam Split i) ≪ size k
                            Q₀ = Split .famprops i
                            Q₁ : size (g ⁻¹* fam Split i) ≪ size k
                            Q₁ = transport-Str (cong-Str (λ ξ -> ξ ≪ size k) (sym-≣ p)) Q₀
                        in IH (size (g ⁻¹* Split .fam i)) Q₁ (g ⁻¹* fam Split i) refl-≣
                      )
                      (λ p ->
                        let Q₀ : size (fam Split i) ≪ size k
                            Q₀ = Split .famprops i
                            Q₁ : size (g ⁻¹* fam Split i) ≪ size k
                            Q₁ = p ⟡-≪ Q₀
                        in IH (size (g ⁻¹* Split .fam i)) Q₁ (g ⁻¹* fam Split i) refl-≣
                      )
          P₁ = lem-45 (Split .fam) P₀
      in transp-isEpiPrincipal (Split .covers) P₁

  isPrincipal:Family : ∀ s -> P s
  isPrincipal:Family = WFI.induction wellFounded lem-50

