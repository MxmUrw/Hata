
module Verification.Core.Order.DedekindCompletion.Instance.Ring where

open import Verification.Conventions
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Rational.Definition

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Order.DedekindCompletion.Definition3
-- open import Verification.Core.Order.DedekindCompletion.Instance.Linearorder
open import Verification.Core.Order.Linearorder



module _ {𝑖 : 𝔏 ^ 3} {𝑘 : 𝔏} {X : Linearorder 𝑖} where
  instance
    isLinearorder:Cut : isLinearorder _ ′ Cut X 𝑘 ′
    isLinearorder.my< isLinearorder:Cut = _<-Cut_
    isLinearorder.irrefl-< isLinearorder:Cut = {!!}
    isLinearorder.asym-< isLinearorder:Cut = {!!}
    isLinearorder.compare-< isLinearorder:Cut = {!!}
    isLinearorder.connected-< isLinearorder:Cut = {!!}
    isLinearorder.transp-< isLinearorder:Cut = {!!}


module _ {𝑖 : 𝔏} (X : Linearorder (𝑖 , 𝑖 , 𝑖))
         {{_ : isUnbound X}}
         {{_ : isDense X}}
  where
  instance
    isSubsetoid':< : ∀{a : ⟨ X ⟩} -> isSubsetoid' (λ x -> ∣ x < a ∣)
    isSubsetoid'.transp-Subsetoid' isSubsetoid':< p = transp-< p refl

    isSubsetoid':<2 : ∀{a : ⟨ X ⟩} -> isSubsetoid' (λ x -> ∣ a < x ∣)
    isSubsetoid'.transp-Subsetoid' isSubsetoid':<2 p = transp-< refl p

  return-Cut : ⟨ X ⟩ -> Cut X 𝑖
  ⩘ (return-Cut x) = ′ (λ a -> ∣ a < x ∣) ′
  ⩗ (return-Cut x) = ′ (λ a -> ∣ x < a ∣) ′
  isCut.inhabited-⩘ (isCutProof (return-Cut x)) = getLess x
  isCut.inhabited-⩗ (isCutProof (return-Cut x)) = getGreater x
  isCut.open-⩘ (isCutProof (return-Cut x)) {a} a<x = let (z ∢ (p , q)) = between a<x in (z ∢ q) , p
  isCut.open-⩗ (isCutProof (return-Cut x)) {a} x<a = let (z ∢ (p , q)) = between x<a in (z ∢ p) , q
  isCut.compare-Cut (isCutProof (return-Cut x)) {a} {b} a<b = compare-< a<b x
  isCut.by-⩘⩗-< (isCutProof (return-Cut x)) {a} {b} p q = p ∙-< q

  instance
    isSetoidHom:return-Cut : isSetoidHom ′ ⟨ X ⟩ ′ ′ Cut X 𝑖 ′ (return-Cut)
    isSetoidHom.preserves-∼ isSetoidHom:return-Cut p = {!!} -- incl (incl ((transp-< refl p) , transp-< refl (sym p)) , incl (transp-< p refl , transp-< (sym p) refl))

{-

  -- sup-Cut : Subsetoid' ′ Cut X 𝑖 ′ 𝑖 -> Subsetoid' ′ ⟨ X ⟩ ′ 𝑖
  -- sup-Cut Cs =
  --   let P = Cs -- ∀(c) -> ⟨ Cs ⟩ c -> {!!}
  --   in ′ (λ a -> ⟨ Cs ⟩ (return-Cut a)) ′ {{{!!}}}

  private
    lower-Cut : (Cut X 𝑖 -> 𝒰 𝑖) -> ⟨ X ⟩ -> 𝒰 𝑖
    lower-Cut C x = C (return-Cut x)

    sup-Cut : (Cut X 𝑖 -> 𝒰 𝑖) -> ⟨ X ⟩ -> 𝒰 (𝑖 ⁺)
    sup-Cut C x = ∑ λ c -> C c ×-𝒰 (x ∈ ⟨ ⩘ c ⟩)

    inf-Cut : (Cut X 𝑖 -> 𝒰 𝑖) -> ⟨ X ⟩ -> 𝒰 (𝑖 ⁺)
    inf-Cut C x = ∑ λ c -> C c ×-𝒰 (x ∈ (⩗ c))

    equiv-lower-sup : ∀(C : Cut ′ Cut X 𝑖 ′ 𝑖) -> ∀{x} -> lower-Cut (⟨ ⩘ C ⟩) x -> sup-Cut (⟨ ⩘ C ⟩) x
    equiv-lower-sup (⩘C , ⩗C) {x} p =
      let ((⩘r , ⩗r) ∢ rP) , (incl (y , x<y , y∢⩘r)) = open-⩘ p
      in (⩘r , ⩗r) , rP , closed-⩘ x<y y∢⩘r

    equiv-lower-sup⁻¹ : ∀(C : Cut ′ Cut X 𝑖 ′ 𝑖) -> ∀{x} -> sup-Cut (⟨ ⩘ C ⟩) x -> lower-Cut (⟨ ⩘ C ⟩) x
    equiv-lower-sup⁻¹ (⩘C , ⩗C) {x} ((⩘r , ⩗r) , r∢C , x∢⩘r) =
      let (y ∢ yP) , x<y = open-⩘ x∢⩘r
          P₀ : return-Cut x < (⩘r , ⩗r)
          P₀ = incl (y , x<y , yP)
      in closed-⩘ P₀ r∢C

    instance
      isSubsetoid':sup-Cut : ∀{Cs : Cut X 𝑖 -> 𝒰 𝑖} {{_ : isSubsetoid' Cs}} -> isSubsetoid' (sup-Cut Cs)
      isSubsetoid':sup-Cut = {!!}

      isSubsetoid':inf-Cut : ∀{Cs : Cut X 𝑖 -> 𝒰 𝑖} {{_ : isSubsetoid' Cs}} -> isSubsetoid' (inf-Cut Cs)
      isSubsetoid':inf-Cut = {!!}

    isCut:supinf : (C : Cut ′ Cut X 𝑖 ′ 𝑖) -> isCut X _ (′ sup-Cut (⟨ ⩘ C ⟩) ′) (′ inf-Cut (⟨ ⩗ C ⟩) ′)
    isCut.inhabited-⩘ (isCut:supinf (⩘C , ⩗C)) =
      let c : ⦋ ⟨ ⩘C ⟩ ⦌
          c = inhabited-⩘
          -- (c' ∢ cP) = c
          x : ⦋ ⟨ ⩘ ⟨ c ⟩ ⟩ ⦌
          x = inhabited-⩘
      in ⟨ x ⟩ ∢ (⟨ c ⟩ , (c .Proof) , (x .Proof))
    isCut.inhabited-⩗ (isCut:supinf C) = {!!}
    isCut.open-⩘ (isCut:supinf C) = {!!}
    isCut.open-⩗ (isCut:supinf C) = {!!}
    isCut.compare-Cut (isCut:supinf C) = {!!}
    isCut.by-⩘⩗-< (isCut:supinf C) = {!!}

  instance
    isSubsetoid':lower-Cut : ∀{Cs : Cut X 𝑖 -> 𝒰 𝑖} {{_ : isSubsetoid' Cs}} -> isSubsetoid' (lower-Cut Cs)
    isSubsetoid'.transp-Subsetoid' (isSubsetoid':lower-Cut {Cs}) p a = transp-Subsetoid' {{make∑i {_} {{isSetoid:Cut}}}} (preserves-∼ p) a
    -- isSubsetoid'.transp-Subsetoid' (isSubsetoid':lower-Cut {Cs}) p a = transp-Subsetoid' {{make∑i {_} {{isSetoid:Cut}}}} (preserves-∼ p) a

  join-Cut : Cut ′ Cut X 𝑖 ′ 𝑖 -> Cut X 𝑖
  ⩘ (join-Cut (⩘x , ⩗x)) = ′ lower-Cut ⟨ ⩘x ⟩ ′
  ⩗ (join-Cut (⩘x , ⩗x)) = {!!}
  isCutProof (join-Cut (⩘x , ⩗x)) = {!!}




{-
-}


{-

module _ {𝑖 : 𝔏} {𝑗 : 𝔏} (X : Linearorder (𝑖 , 𝑗 , 𝑖)) {{_ : isMonoid ′ ⟨ X ⟩ ′}} where
  _⋆-Cut_ : Cut X -> Cut X -> Cut X
  _⋆-Cut_ (⩘a , ⩗a) (⩘b , ⩗b) =
    let x = ⩘a
        ⩘c = {!!}
    in (⩘c , {!!}) {{{!!}}}

  ◌-Cut : Cut X
  ⩘ ◌-Cut = ′ (λ x -> x < ◌) ′ {{{!!}}}
  ⩗ ◌-Cut = ′ (λ x -> ◌ < x) ′ {{{!!}}}
  isCut.inhabited-⩘ (isCutProof ◌-Cut) = {!!}
  isCut.inhabited-⩗ (isCutProof ◌-Cut) = {!!}
  isCut.open-⩘ (isCutProof ◌-Cut) = {!!}
  isCut.open-⩗ (isCutProof ◌-Cut) = {!!}
  isCut.compare-Cut (isCutProof ◌-Cut) = {!!}
  isCut.by-⩘⩗-< (isCutProof ◌-Cut) p q = p ∙-< q
-}

  -- instance
  --   isMonoid:Cut : isMonoid ′ Cut X ′
  --   isMonoid._⋆_ isMonoid:Cut = {!!}
  --   isMonoid.◌ isMonoid:Cut = {!!}
  --   isMonoid.unit-l-⋆ isMonoid:Cut = {!!}
  --   isMonoid.unit-r-⋆ isMonoid:Cut = {!!}
  --   isMonoid.assoc-l-⋆ isMonoid:Cut = {!!}
  --   isMonoid.assoc-r-⋆ isMonoid:Cut = {!!}
  --   isMonoid._`cong-⋆`_ isMonoid:Cut = {!!}




-}

