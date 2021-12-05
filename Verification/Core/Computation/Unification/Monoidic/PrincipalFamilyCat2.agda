
module Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2 where

open import Verification.Conventions

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Subsetoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Core.Theory.Presentation.Signature.Definition


module _ {M : 𝒰 𝑖} {{_ : Monoid₀ (𝑖 , 𝑖) on M}} where

  record CoeqSolutions' (f g h : M) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : f ⋆ h ∼ g ⋆ h
  open CoeqSolutions' public

  CoeqSolutions : (f g : M) -> 𝒫 M
  CoeqSolutions f g = λ h -> ∣ CoeqSolutions' f g h ∣

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record hasProperty-isCoeq {a b x : 𝒞} (f : (a ⟶ b) ^ 2) (h : b ⟶ x) : 𝒰 (𝑖 ､ 𝑗) where
    constructor incl
    field ⟨_⟩ : fst f ◆ h ∼ snd f ◆ h

module _ {M : Monoid₀ (𝑖 , 𝑖)} {f g : ⟨ M ⟩} where
  instance
    isSubsetoid:CoeqSolutions : isSubsetoid (CoeqSolutions f g)
    isSubsetoid.transp-Subsetoid isSubsetoid:CoeqSolutions (p) (incl P) = incl ((refl ≀⋆≀ p ⁻¹) ∙ P ∙ (refl ≀⋆≀ p))

  instance
    isIdeal-r:CoeqSolutions : isIdeal-r M ′(CoeqSolutions f g)′
    isIdeal-r.ideal-r-⋆ isIdeal-r:CoeqSolutions {h} (incl P) i =
      let P₀ : f ⋆ (h ⋆ i) ∼ g ⋆ (h ⋆ i)
          P₀ = f ⋆ (h ⋆ i)   ⟨ assoc-r-⋆ ⟩-∼
                (f ⋆ h) ⋆ i   ⟨ P ≀⋆≀ refl ⟩-∼
                (g ⋆ h) ⋆ i   ⟨ assoc-l-⋆ ⟩-∼
                g ⋆ (h ⋆ i)   ∎
      in incl P₀
    isIdeal-r.ideal-◍ isIdeal-r:CoeqSolutions = incl (absorb-r-⋆ ∙ absorb-r-⋆ ⁻¹)
-- private
module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory {𝑖} 𝒞}} where
  Pair : (a b : 𝒞) -> 𝒰 _
  Pair a x = Hom a x ×-𝒰 Hom a x

IxC : (𝒞 : Category 𝑖) -> 𝒰 _
IxC 𝒞 = ∑ λ (a : ⟨ 𝒞 ⟩) -> ∑ λ b -> Pair a b

module _ (𝒞 : Category 𝑖) {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} where
  𝓘C : (i : IxC 𝒞) -> Ideal-r ′(PathMon 𝒞)′
  𝓘C (_ , _ , f , g) = ′ (CoeqSolutions (arrow f) (arrow g)) ′

-- module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑘} 𝒞}} {{_ : isDiscrete 𝒞}} {{_ : isSet-Str 𝒞}} where
  -- data isPrincipalC {a b : 𝒞} (f g : a ⟶ b) : 𝒰 𝑖 where
  --   solved : hasCoequalizer f g
  --   field princobj : 




module _ (𝒞 : SizedCategory 𝑖) where
  record isSplittableC (n : 人ℕ) {a b : ⟨ 𝒞 ⟩} (f : (a ⟶ b) ^ 2) : 𝒰 𝑖 where
    field famC : n ∍ tt -> ∑ λ a' -> (Pair a' b)
    field coversC : ∀{x} -> (h : b ⟶ x) -> (f ⌄ 0 ◆ h ∼ f ⌄ 1 ◆ h) ↔ (∀ p -> (famC p .snd) ⌄ 0 ◆ h ∼ (famC p .snd) ⌄ 1 ◆ h)
    -- field coversC : ⋀-fin (λ i -> 𝓘C 𝒞 (famC i)) ∼ 𝓘C 𝒞 i
    field fampropsC : ∀ k -> sizeC (famC k .snd) ≪ sizeC f
    -- P (_ , _ , f) (_ , _ , famC k .snd)
  open isSplittableC public

record isPrincipalFamilyCat (𝒞 : SizedCategory 𝑖) : 𝒰 (𝑖 ⁺) where
  field isBase : ∀{a x : ⟨ 𝒞 ⟩} -> (Pair a x) -> 𝒰 (𝑖 ⌄ 1)
  field ∂C : ∀{x y : ⟨ 𝒞 ⟩} -> (i : Pair x y)
           -> (isBase i +-𝒰 (∑ λ n -> isSplittableC 𝒞 n i))
  field isPrincipalC:Base : ∀{a b : ⟨ 𝒞 ⟩} -> ∀(f g : a ⟶ b) -> isBase (f , g) -> ¬ (hasCoequalizer f g) +-𝒰 (hasReducingCoequalizer f g)

open isPrincipalFamilyCat {{...}} public

{-
module _ (𝒞 : Category 𝑖) {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} where
  record isSplittableC (n : 人ℕ) {a b : ⟨ 𝒞 ⟩} (f : (a ⟶ b) ^ 2) (P : IxC 𝒞 -> IxC 𝒞 -> 𝒰₀) : 𝒰 𝑖 where
    field famC : n ∍ tt -> ∑ λ a' -> (Pair a' b)
    field coversC : ∀{x} -> (h : b ⟶ x) -> (f ⌄ 0 ◆ h ∼ f ⌄ 1 ◆ h) ↔ (∀ p -> (famC p .snd) ⌄ 0 ◆ h ∼ (famC p .snd) ⌄ 1 ◆ h)
    -- field coversC : ⋀-fin (λ i -> 𝓘C 𝒞 (famC i)) ∼ 𝓘C 𝒞 i
    field fampropsC : ∀ k -> P (_ , _ , f) (_ , _ , famC k .snd)
  open isSplittableC public

record isPrincipalFamilyCat (𝒞 : Category 𝑖) {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} : 𝒰 (𝑖 ⁺) where
  field SizeC : WFT (ℓ₀ , ℓ₀)
  field isBase : ∀{a x : ⟨ 𝒞 ⟩} -> (Pair a x) -> 𝒰 (𝑖 ⌄ 1)
  field sizeC : {a x : ⟨ 𝒞 ⟩} -> (Pair a x) -> ⟨ SizeC ⟩

  -- field SizeCF : WFT (ℓ₀ , ℓ₀)
  -- field sizeC : (x : ⟨ 𝒞 ⟩) -> ⟨ SizeC ⟩
  -- field sizeCF : {x : ⟨ 𝒞 ⟩} -> (Pair a x) -> ⟨ SizeCF ⟩
  -- field _≪_ : SizeC -> SizeC -> 𝒰₀
  -- field trans-SizeC : ∀{a b c} -> a ≪ b -> b ≪ c -> a ≪ c
  -- field isWellFounded:SizeC : WellFounded _≪_
  -- _⪣_ : SizeC -> SizeC -> 𝒰₀
  -- a ⪣ b = (a ≡-Str b) ∨ (a ≪ b)

  field ∂C : ∀{x y : ⟨ 𝒞 ⟩} -> (i : Pair x y)
           -> (isBase (i)
              +-𝒰 (∑ λ n -> isSplittableC 𝒞 n i (λ (_ , _ , i) -> λ (_ , _ , j) -> sizeC j ≪ sizeC i)))

  field size0 : ⟨ SizeC ⟩
  field initial-size0 : ∀{a} -> size0 ⪣ a
  field isPrincipalC:Base : ∀{a b : ⟨ 𝒞 ⟩} -> ∀(f g : a ⟶ b) -> isBase (f , g) -> isDecidable (hasCoequalizer f g)
  -}


data Side : 𝒰₀ where
  isLeft isRight : Side

module _ (𝒞 : Category (𝑖 , 𝑖 , 𝑖)) {{X : isSizedCategory 𝒞}} {{F : isPrincipalFamilyCat ′ ⟨ 𝒞 ⟩ ′}} where
  private

    -- Ix generates our ideals
    -- Bx determines those which are base ideals, and thus trivially principal/good/+
    -- If Ix is nothing, this means that this is the whole monoid, i.e., the
    -- two arrows are already equal, we have no constraints

    Ix = Maybe (∑ λ (a : ⟨ 𝒞 ⟩) -> ∑ λ (x : ⟨ 𝒞 ⟩) -> Pair a x)
    Bx = Maybe (∑ λ (a : ⟨ 𝒞 ⟩) -> ∑ λ (x : ⟨ 𝒞 ⟩) -> ∑ isBase {a = a} {x})
    -- Side ×-𝒰 ((∑ isBase a x) ∧ Hom a x))

    -- record isSplittableCat (n : ℕ) (i : Ix) (P : I -> 𝒰₀) : 𝒰 (𝑗 ､ 𝑖 ⁺) where
    --   field fam : Fin-R n -> I
    --   field covers : ⋀-fin (λ i -> 𝓘 (fam i)) ∼ 𝓘 i
    --   field famprops : ∀ k -> P (fam k)
    -- open isSplittable public

    size' : Ix -> ⟨ SizeC ⟩
    size' nothing = ⊥-WFT
    size' (just (a , x , f)) = sizeC f

    bb : Bx -> Ix
    bb nothing = nothing
    bb (just (x , a , (f , g) , _)) = just (x , a , (f , g))
    -- bb (just (x , a , isLeft , ((h , _) , f)))  = just (x , a , h , f)
    -- bb (just (x , a , isRight , ((h , _) , f))) = just (x , a , f , h)


    M : Monoid₀ _
    M = ′ PathMon 𝒞 ′

    𝓘 : Ix -> Ideal-r M
    𝓘 nothing = ⊤
    𝓘 (just (_ , _ , f , g)) = ′(CoeqSolutions (arrow f) (arrow g))′

    Good : 𝒫 (PathMon 𝒞)
    Good [] = ⊤
    Good idp = ⊤
    Good (arrow {x} {y} h) = ∣ (∀(a : ⟨ 𝒞 ⟩) -> (f g : a ⟶ x) -> sizeC (f ◆ h , g ◆ h) ≪ sizeC (f , g)) ∣


    _⁻¹'_ : ⦋ Good ⦌ -> Ix -> Ix
    _⁻¹'_ (a) nothing = nothing
    _⁻¹'_ ([] ∢ _) (just _) = nothing
    _⁻¹'_ (idp ∢ _) (just x) = just x
    _⁻¹'_ (arrow {a} {b} h ∢ _) (just (y , x , (f , g))) with (x ≟-Str a)
    ... | yes refl-≣ = just (y , b , (f ◆ h) , (g ◆ h))
    ... | no ¬p = nothing

    lem-100 : {a b : PathMon 𝒞} → a ∼-PathMon b → a ∈ Good → b ∈ Good
    lem-100 idp = id-𝒰
    lem-100 [] = id-𝒰
    lem-100 (arrow p) = {!!}

    instance
      isSubsetoid:Good : isSubsetoid Good
      isSubsetoid:Good = record { transp-Subsetoid = lem-100 }
      -- isSubsetoid.transp-Subsetoid isSubsetoid:Good (incl idp) P = tt
      -- isSubsetoid.transp-Subsetoid isSubsetoid:Good (incl []) P = P
      -- isSubsetoid.transp-Subsetoid isSubsetoid:Good (incl (arrow f∼g)) (↥ p) = ↥ p

      isSubmonoid:Good : isSubmonoid ′ Good ′
      isSubmonoid:Good = record { closed-◌ = tt ; closed-⋆ = {!!} }
      -- isSubmonoid.closed-◌ isSubmonoid:Good = tt
      -- isSubmonoid.closed-⋆ isSubmonoid:Good {idp} {b} p1 p2 = p2
      -- isSubmonoid.closed-⋆ isSubmonoid:Good {[]} {b} p1 p2 = p1
      -- isSubmonoid.closed-⋆ isSubmonoid:Good {arrow f} {[]} p1 p2 = p2
      -- isSubmonoid.closed-⋆ isSubmonoid:Good {arrow f} {idp} p1 p2 = p1
      -- isSubmonoid.closed-⋆ isSubmonoid:Good {arrow {a} {b} f} {arrow {c} {d} g} (↥ p1) (↥ p2) with (b ≟-Str c)


    lem-10 : (g : ⦋ Good ⦌) (i : Ix) → (size' (g ⁻¹' i) ⪣ size' i)
    lem-10 g nothing = left refl-≣
    lem-10 ([] ∢ gp) (just x) = elim-⊥-WFT
    lem-10 (idp ∢ gp) (just x) = left refl-≣
    lem-10 (arrow {a} {b} h ∢ (hp)) (just (y , x , f , g)) with (x ≟-Str a)
    ... | no ¬p = elim-⊥-WFT
    ... | yes refl-StrId = right (hp _ f g)

    lem-20 : {g : ⦋ Good ⦌} {i : Ix} → 𝓘 (g ⁻¹' i) ∼ (⟨ g ⟩ ⁻¹↷-Ide 𝓘 i)
    lem-20 = {!!}
    -- lem-20 {g ∢ gp} {nothing} = unit-r-⁻¹↷-Ide ⁻¹
    -- lem-20 {[] ∢ gp} {just (x , (f , g))} = absorb-l-⁻¹↷-Ide ⁻¹
    -- lem-20 {idp ∢ gp} {just (x , (f , g))} = unit-l-⁻¹↷-Ide ⁻¹
    -- lem-20 {arrow {a} {b} h ∢ gp} {just (x , (f , g))} with (x ≟-Str a)
    -- ... | no ¬p =
    --   let P₀ : ⊤ ≤ ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′)
    --       P₀ = incl (λ {a} x₁ → incl (incl (
    --                 arrow f ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow f} {b = arrow h} ⟩-∼
    --                 (arrow f ⋆ arrow h) ⋆ a    ⟨ PathMon-non-matching-arrows ¬p f h ≀⋆≀ refl ⟩-∼
    --                 [] ⋆ a                     ⟨ PathMon-non-matching-arrows ¬p g h ⁻¹ ≀⋆≀ refl ⟩-∼
    --                 (arrow g ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow g} {b = arrow h} ⟩-∼
    --                 arrow g ⋆ (arrow h ⋆ a)    ∎
    --            )))
    --   in antisym P₀ terminal-⊤
    -- ... | yes refl-StrId =
    --   let P₀ : ′(CoeqSolutions (arrow (f ◆ h)) (arrow (g ◆ h)))′ ≤ ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′)
    --       P₀ = incl (λ {a} (incl P) → incl (incl (
    --                 arrow f ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow f} {b = arrow h} ⟩-∼
    --                 (arrow f ⋆ arrow h) ⋆ a    ⟨ functoriality-arrow f h ⁻¹ ≀⋆≀ refl ⟩-∼
    --                 (arrow (f ◆ h)) ⋆ a        ⟨ P ⟩-∼
    --                 (arrow (g ◆ h)) ⋆ a        ⟨ functoriality-arrow g h ≀⋆≀ refl ⟩-∼
    --                 (arrow g ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow g} {b = arrow h} ⟩-∼
    --                 arrow g ⋆ (arrow h ⋆ a)    ∎
    --            )))
    --       P₁ : ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′) ≤ ′(CoeqSolutions (arrow (f ◆ h)) (arrow (g ◆ h)))′
    --       P₁ = incl (λ {a} (incl (incl P)) → incl (
    --                 (arrow (f ◆ h)) ⋆ a        ⟨ functoriality-arrow f h ≀⋆≀ refl ⟩-∼
    --                 (arrow f ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow f} {b = arrow h} ⟩-∼
    --                 arrow f ⋆ (arrow h ⋆ a)    ⟨ P ⟩-∼
    --                 arrow g ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow g} {b = arrow h} ⟩-∼
    --                 (arrow g ⋆ arrow h) ⋆ a    ⟨ functoriality-arrow g h ⁻¹ ≀⋆≀ refl ⟩-∼
    --                 (arrow (g ◆ h)) ⋆ a        ∎
    --            ))
    --   in antisym P₀ P₁

{-
    lem-20 : {g : ⦋ Good ⦌} {i : Ix} → 𝓘 (g ⁻¹' i) ∼ (⟨ g ⟩ ⁻¹↷-Ide 𝓘 i)
    lem-20 {g ∢ gp} {nothing} = unit-r-⁻¹↷-Ide ⁻¹
    lem-20 {[] ∢ gp} {just (x , (f , g))} = absorb-l-⁻¹↷-Ide ⁻¹
    lem-20 {idp ∢ gp} {just (x , (f , g))} = unit-l-⁻¹↷-Ide ⁻¹
    lem-20 {arrow {a} {b} h ∢ gp} {just (x , (f , g))} with (x ≟-Str a)
    ... | no ¬p =
      let P₀ : ⊤ ≤ ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′)
          P₀ = incl (λ {a} x₁ → incl (incl (
                    arrow f ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow f} {b = arrow h} ⟩-∼
                    (arrow f ⋆ arrow h) ⋆ a    ⟨ PathMon-non-matching-arrows ¬p f h ≀⋆≀ refl ⟩-∼
                    [] ⋆ a                     ⟨ PathMon-non-matching-arrows ¬p g h ⁻¹ ≀⋆≀ refl ⟩-∼
                    (arrow g ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow g} {b = arrow h} ⟩-∼
                    arrow g ⋆ (arrow h ⋆ a)    ∎
               )))
      in antisym P₀ terminal-⊤
    ... | yes refl-StrId =
      let P₀ : ′(CoeqSolutions (arrow (f ◆ h)) (arrow (g ◆ h)))′ ≤ ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′)
          P₀ = incl (λ {a} (incl P) → incl (incl (
                    arrow f ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow f} {b = arrow h} ⟩-∼
                    (arrow f ⋆ arrow h) ⋆ a    ⟨ functoriality-arrow f h ⁻¹ ≀⋆≀ refl ⟩-∼
                    (arrow (f ◆ h)) ⋆ a        ⟨ P ⟩-∼
                    (arrow (g ◆ h)) ⋆ a        ⟨ functoriality-arrow g h ≀⋆≀ refl ⟩-∼
                    (arrow g ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow g} {b = arrow h} ⟩-∼
                    arrow g ⋆ (arrow h ⋆ a)    ∎
               )))
          P₁ : ((arrow h) ⁻¹↷-Ide ′(CoeqSolutions (arrow f) (arrow g))′) ≤ ′(CoeqSolutions (arrow (f ◆ h)) (arrow (g ◆ h)))′
          P₁ = incl (λ {a} (incl (incl P)) → incl (
                    (arrow (f ◆ h)) ⋆ a        ⟨ functoriality-arrow f h ≀⋆≀ refl ⟩-∼
                    (arrow f ⋆ arrow h) ⋆ a    ⟨ assoc-l-⋆ {a = arrow f} {b = arrow h} ⟩-∼
                    arrow f ⋆ (arrow h ⋆ a)    ⟨ P ⟩-∼
                    arrow g ⋆ (arrow h ⋆ a)    ⟨ assoc-r-⋆ {a = arrow g} {b = arrow h} ⟩-∼
                    (arrow g ⋆ arrow h) ⋆ a    ⟨ functoriality-arrow g h ⁻¹ ≀⋆≀ refl ⟩-∼
                    (arrow (g ◆ h)) ⋆ a        ∎
               ))
      in antisym P₀ P₁
      -}

    lem-30 : ∀(i : Ix) -> (∑ λ b -> 𝓘 (bb b) ∼ 𝓘 i) +-𝒰 (∑ λ n -> isSplittable M ′ Good ′ bb 𝓘 n i (λ j -> size' j ≪ size' i))
    lem-30 = {!!}


      -- ... | yes refl-StrId = ↥ (p2 ⟡-≪ p1)
      -- ... | no ¬p = tt
      -- record
      --   { closed-◌ = tt
      --   ; closed-⋆ = λ p1 p2 -> ?
      --   }

  by-PrincipalCat-Principal : isPrincipalFamily M ′ Good ′ bb 𝓘
  by-PrincipalCat-Principal = {!!}
  -- record
  --              { Size = SizeC
  --              ; size = size'
  --              ; _⁻¹*_ = _⁻¹'_
  --              ; size:⁻¹* = lem-10
  --              ; preserves-𝓘:⁻¹* = λ {g} {i} -> lem-20 {g} {i}
  --              ; ∂ = lem-30
  --              ; principalBase = {!!}
  --              }

    -- lem-10 : (g : ⦋ Good ⦌) (i : Ix) → (size' (g ⁻¹' i) ⪣ size' i)
    -- lem-10 (g ∢ gp) nothing = left refl
    -- lem-10 ([] ∢ hp) (just (x , (f , g))) = initial-size0
    -- lem-10 (idp ∢ hp) (just (x , (f , g))) = left refl
    -- lem-10 (arrow {a} {b} h ∢ (↥ hp)) (just (x , (f , g))) with (x ≟-Str a)
    -- ... | no ¬p = initial-size0
    -- ... | yes refl-StrId = right hp


  -- module _ {B I : 𝒰₀} (𝒷 : B -> I) (𝓘 : I -> Ideal-r M) where

      -- field size : I -> Size
      -- field _<<_ : Size -> Size -> 𝒰₀
      -- field isWellFounded:Size : WellFounded _<<_
      -- field trans-Size : ∀{a b c} -> a << b -> b << c -> a << c
      -- field _⁻¹*_ : ⦋ ⟨ Good ⟩ ⦌ -> I -> I
      -- field size:⁻¹* : ∀ g i -> (size (g ⁻¹* i) ≡-Str size i) +-𝒰 (size (g ⁻¹* i) << size i)
      -- field preserves-𝓘:⁻¹* : ∀ {g i} -> 𝓘 (g ⁻¹* i) ∼ (⟨ g ⟩ ⁻¹↷-Ide (𝓘 i))
      -- -- field 𝓘 : Idx -> Ideal-r M
      -- field ∂ : (i : I) -> (∑ λ b -> 𝒷 b ≡-Str i) +-𝒰 (∑ λ n -> isSplittable n i (λ j -> size j << size i))
      -- field principalBase : ∀ b -> isPrincipal/⁺-r Good (𝓘 (𝒷 b))
