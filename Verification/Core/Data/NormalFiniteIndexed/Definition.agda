
module Verification.Core.Data.NormalFiniteIndexed.Definition where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Contradiction
-- open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.Iso.Property
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Universe.Instance.SeparatingFamily

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Xiix
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Indexed.Instance.SeparatingFamily
open import Verification.Core.Data.Indexed.Property.Iso

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.Monoid.Free.Element

open import Verification.Core.Category.Std.Category.Subcategory.Full public
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Core.Data.FiniteIndexed.Definition


module _ {I : 𝒰 𝑖} where

  ι-♮𝐅𝐢𝐧𝐈𝐱 : List I -> 𝐅𝐢𝐧𝐈𝐱 I
  ι-♮𝐅𝐢𝐧𝐈𝐱 as = incl (ι as)

module _ (I : 𝒰 𝑖) where

  NormalFiniteIndexed : 𝒰 _
  NormalFiniteIndexed = 𝐅𝐮𝐥𝐥 (𝐅𝐢𝐧𝐈𝐱 I) ι-♮𝐅𝐢𝐧𝐈𝐱

  macro ♮𝐅𝐢𝐧𝐈𝐱 = #structureOn NormalFiniteIndexed

  -- instance
  --   isIso:ι-Free-𝐌𝐨𝐧 : isIso {𝒞 = } (hom ι-Free-𝐌𝐨𝐧)
  --   isIso:ι-Free-𝐌𝐨𝐧 = {!!}




module _ {I : 𝒰 𝑖} where

  instance
    hasNormalization:♮𝐅𝐢𝐧𝐈𝐱 : hasNormalization (𝐅𝐢𝐧𝐈𝐱 I) (♮𝐅𝐢𝐧𝐈𝐱 I)
    hasNormalization:♮𝐅𝐢𝐧𝐈𝐱 = normalization (λ x → incl (♮ ⟨ x ⟩))

  private
    module _ where
      abstract
        lem-10 : {as bs : List I} -> (ι (as ⋆ bs) ∼ ι as ⋆ ι bs)
        lem-10 {⦋⦌} {bs} = unit-l-⋆ ⁻¹
        lem-10 {x ∷ as} {bs} = (refl ≀⋆≀ lem-10 {as} {bs}) ∙ assoc-r-⋆

    f : ∀{a : I} -> {as : Free-𝐌𝐨𝐧 I} -> as ∍ a -> ι (♮ as) ∍ a
    f incl = left-∍ incl
    f {a} (right-∍ {as} {bs} p) = -- ⟨ cong-∼ (lem-10 ⁻¹) ⟩ a (right-∍ (f p))
      let q : ι (♮ as) ⋆ ι (♮ bs) ∼ ι (♮ as ⋆ ♮ bs)
          q = lem-10 {as = ♮ as} {♮ bs} ⁻¹
          q₂ : 𝑒𝑙 (ι (♮ as) ⋆ ι (♮ bs)) ∼ 𝑒𝑙 (ι (♮ as ⋆ ♮ bs))
          q₂ = cong-∼ q
          r : (ι (♮ as) ⋆ ι (♮ bs)) ∍ a
          r = right-∍ (f p)
      in ⟨ q₂ ⟩ a r
    f {a} (left-∍ {as} {bs} p) =
      let q : ι (♮ as) ⋆ ι (♮ bs) ∼ ι (♮ as ⋆ ♮ bs)
          q = lem-10 {as = ♮ as} {♮ bs} ⁻¹
          q₂ : 𝑒𝑙 (ι (♮ as) ⋆ ι (♮ bs)) ∼ 𝑒𝑙 (ι (♮ as ⋆ ♮ bs))
          q₂ = cong-∼ q
          r : (ι (♮ as) ⋆ ι (♮ bs)) ∍ a
          r = left-∍ (f p)
      in ⟨ q₂ ⟩ a r

    g : ∀{a : I} -> {as : Free-𝐌𝐨𝐧 I} -> ι (♮ as) ∍ a -> as ∍ a
    g {as = incl x} (left-∍ p) = p
    g {a} {as = as ⋆-Free-𝐌𝐨𝐧 bs} p with ⟨ cong-∼ (lem-10 {as = ♮ as} {♮ bs}) ⟩ a p
    ... | right-∍ X = right-∍ (g X)
    ... | left-∍ X = left-∍ (g X)

    lem-15 : ∀{a : I} {as : Free-𝐌𝐨𝐧 I} -> (p : ι (♮ as) ∍ a) -> f {a} {as} (g p) ≡ p
    lem-15 {.x} {incl x} (left-∍ incl) = refl-≡
    lem-15 {a} {as ⋆-Free-𝐌𝐨𝐧 bs} p with ⟨ cong-∼ (lem-10 {as = ♮ as} {♮ bs}) ⟩ a p in ip
    ... | left-∍ X = ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (left-∍ (f {a} {as} (g X)))

                       ⟨ (λ i -> ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (left-∍ (lem-15 {a} {as} X i)))  ⟩-≡

                     ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (left-∍ X)

                       ⟨ (λ i -> ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (≡-Str→≡ ip (~ i))) ⟩-≡

                     ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (⟨ (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a p)

                       ⟨ (λ i -> (inv-r-◆ (of (cong-∼ (lem-10 {as = ♮ as} {♮ bs})))) a i p) ⟩-≡

                     p                                                                            ∎-≡

    ... | right-∍ X = ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (right-∍ (f {a} {bs} (g X)))

                       ⟨ (λ i -> ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (right-∍ (lem-15 {a} {bs} X i)))  ⟩-≡

                     ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (right-∍ X)

                       ⟨ (λ i -> ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (≡-Str→≡ ip (~ i))) ⟩-≡

                     ⟨ sym (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a (⟨ (cong-∼ (lem-10 {as = ♮ as} {♮ bs})) ⟩ a p)

                       ⟨ (λ i -> (inv-r-◆ (of (cong-∼ (lem-10 {as = ♮ as} {♮ bs})))) a i p) ⟩-≡

                     p                                                                            ∎-≡

    lem-16 : ∀{a : I} {as : Free-𝐌𝐨𝐧 I} -> (p : as ∍ a) -> g {a} {as} (f p) ≡ p
    lem-16 {a} {.(incl a)} incl = refl-≡
    lem-16 {a} {as ⋆-Free-𝐌𝐨𝐧 bs} (right-∍ p) with (⟨ cong-∼ (lem-10 {as = ♮ as} {♮ bs})⟩ a (inverse-◆ (of cong-∼ lem-10) a (right-∍ (f p)))) in ip
    ... | right-∍ X  =
      let q : right-∍ (f p) ≡ right-∍ X
          q = right-∍ (f p)   ⟨ (λ i -> inv-l-◆ (of (cong-∼ (lem-10 {as = ♮ as} {♮ bs}))) a (~ i) (right-∍ (f p))) ⟩-≡
              _              ⟨ ≡-Str→≡ ip ⟩-≡
              right-∍ X       ∎-≡
          q' = cancel-injective-𝒰 q
          q₂ : g {a} {bs} (f p) ≡ g X
          q₂ = cong g q'
          q₃ : p ≡ g X
          q₃ = trans-Path (sym-Path (lem-16 {a} {bs} p)) q₂
      in cong right-∍ (sym-Path q₃)
    ... | left-∍ X =
      let q : right-∍ (f p) ≡ left-∍ X
          q = right-∍ (f p)   ⟨ (λ i -> inv-l-◆ (of (cong-∼ (lem-10 {as = ♮ as} {♮ bs}))) a (~ i) (right-∍ (f p))) ⟩-≡
              _              ⟨ ≡-Str→≡ ip ⟩-≡
              left-∍ X       ∎-≡
      in impossible q


    lem-16 {a} {as ⋆-Free-𝐌𝐨𝐧 bs} (left-∍ p) with ⟨ cong-∼ (lem-10 {as = ♮ as} {♮ bs}) ⟩ a (⟨ cong-∼ (lem-10 ⁻¹) ⟩ a (left-∍ (f p))) in ip
    ... | left-∍ X  =
      let q : left-∍ (f p) ≡ left-∍ X
          q = left-∍ (f p)   ⟨ (λ i -> inv-l-◆ (of (cong-∼ (lem-10 {as = ♮ as} {♮ bs}))) a (~ i) (left-∍ (f p))) ⟩-≡
              _              ⟨ ≡-Str→≡ ip ⟩-≡
              left-∍ X       ∎-≡
          q' = cancel-injective-𝒰 q
          q₂ : g {a} {as} (f p) ≡ g X
          q₂ = cong g q'
          q₃ : p ≡ g X
          q₃ = trans-Path (sym-Path (lem-16 {a} {as} p)) q₂
      in cong left-∍ (sym-Path q₃)
    ... | right-∍ X =
      let q : left-∍ (f p) ≡ right-∍ X
          q = left-∍ (f p)   ⟨ (λ i -> inv-l-◆ (of (cong-∼ (lem-10 {as = ♮ as} {♮ bs}))) a (~ i) (left-∍ (f p))) ⟩-≡
              _              ⟨ ≡-Str→≡ ip ⟩-≡
              right-∍ X       ∎-≡
      in impossible q

    lem-25 : ∀{a : I} -> {as : Free-𝐌𝐨𝐧 I} -> (ι (♮ as) ∍ a) ≅ (as ∍ a)
    lem-25 {a} {as} = g since record
                              { inverse-◆ = f
                              ; inv-r-◆   = funExt (lem-15 {as = as})
                              ; inv-l-◆   = funExt (lem-16)
                              }


  -- we show that the inclusion is essentially surjective, thus ♮𝐅𝐢𝐧𝐈𝐱 ≅ 𝐅𝐢𝐧𝐈𝐱
  private
    F : Functor (♮𝐅𝐢𝐧𝐈𝐱 I) (𝐅𝐢𝐧𝐈𝐱 I)
    F = 𝑓𝑢𝑙𝑙 _ ι-♮𝐅𝐢𝐧𝐈𝐱

  private
    lem-30 : ∀{a : 𝐅𝐢𝐧𝐈𝐱 I} -> ⟨ F ⟩ (♮ a) ≅ a
    lem-30 {a} = cong⁻¹-≅ (construct-≅-𝐈𝐱 lem-25)

  instance
    isEssentiallySurjective:𝑓𝑢𝑙𝑙-♮𝐅𝐢𝐧𝐈𝐱 : isEssentiallySurjective F
    isEssentiallySurjective:𝑓𝑢𝑙𝑙-♮𝐅𝐢𝐧𝐈𝐱 = essentiallysurjective ♮ lem-30



  -- explicit coproducts for ♮𝐅𝐢𝐧𝐈𝐱
  _⊔-♮𝐅𝐢𝐧𝐈𝐱_ : ♮𝐅𝐢𝐧𝐈𝐱 I -> ♮𝐅𝐢𝐧𝐈𝐱 I -> ♮𝐅𝐢𝐧𝐈𝐱 I
  _⊔-♮𝐅𝐢𝐧𝐈𝐱_ a b = incl (⟨ a ⟩ ⋆ ⟨ b ⟩)

  private
    module _ {a b : ♮𝐅𝐢𝐧𝐈𝐱 I} where
      instance
        isCoproduct:⊔-♮𝐅𝐢𝐧𝐈𝐱 : isCoproduct a b (a ⊔-♮𝐅𝐢𝐧𝐈𝐱 b)
        isCoproduct:⊔-♮𝐅𝐢𝐧𝐈𝐱 = {!!}

  instance
    hasCoproducts:♮𝐅𝐢𝐧𝐈𝐱 : hasCoproducts (♮𝐅𝐢𝐧𝐈𝐱 I)
    hasCoproducts._⊔_ hasCoproducts:♮𝐅𝐢𝐧𝐈𝐱 = _⊔-♮𝐅𝐢𝐧𝐈𝐱_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:♮𝐅𝐢𝐧𝐈𝐱 = isCoproduct:⊔-♮𝐅𝐢𝐧𝐈𝐱

  instance
    hasInitial:♮𝐅𝐢𝐧𝐈𝐱 : hasInitial (♮𝐅𝐢𝐧𝐈𝐱 I)
    hasInitial:♮𝐅𝐢𝐧𝐈𝐱 = hasInitial:byFFEso

  -- instance
  --   hasFiniteCoproducts:♮𝐅𝐢𝐧𝐈𝐱 : hasFiniteCoproducts (♮𝐅𝐢𝐧𝐈𝐱 I)
  --   hasFiniteCoproducts:♮𝐅𝐢𝐧𝐈𝐱 = hasFiniteCoproducts:byFFEso





