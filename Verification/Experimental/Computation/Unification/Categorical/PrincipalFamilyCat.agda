
module Verification.Experimental.Computation.Unification.Categorical.PrincipalFamilyCat where

open import Verification.Conventions

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Sized.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Nat.Free
-- open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.WellFounded.Construction.Lexicographic
open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Computation.Unification.Categorical.PrincipalFamily
open import Verification.Experimental.Computation.Unification.Categorical.Definition
open import Verification.Experimental.Category.Std.Category.As.PtdCategory.Definition
open import Verification.Experimental.Category.Std.Category.As.PtdCategory.Coequalizer
-- open import Verification.Experimental.Theory.Presentation.Signature.Definition


-- module _ {M : 𝒰 𝑖} {{_ : Monoid₀ (𝑖 , 𝑖) on M}} where

--   record CoeqSolutions' (f g h : M) : 𝒰 𝑖 where
--     constructor incl
--     field ⟨_⟩ : f ⋆ h ∼ g ⋆ h
--   open CoeqSolutions' public

--   CoeqSolutions : (f g : M) -> 𝒫 M
--   CoeqSolutions f g = λ h -> ∣ CoeqSolutions' f g h ∣

-- module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
--   record hasProperty-isCoeq {a b x : 𝒞} (f : (a ⟶ b) ^ 2) (h : b ⟶ x) : 𝒰 (𝑖 ､ 𝑗) where
--     constructor incl
--     field ⟨_⟩ : fst f ◆ h ∼ snd f ◆ h

-- module _ {M : Monoid₀ (𝑖 , 𝑖)} {f g : ⟨ M ⟩} where
--   instance
--     isSubsetoid:CoeqSolutions : isSubsetoid (CoeqSolutions f g)
--     isSubsetoid.transp-Subsetoid isSubsetoid:CoeqSolutions (p) (incl P) = incl ((refl ≀⋆≀ p ⁻¹) ∙ P ∙ (refl ≀⋆≀ p))

--   instance
--     isIdeal-r:CoeqSolutions : isIdeal-r M ′(CoeqSolutions f g)′
--     isIdeal-r.ideal-r-⋆ isIdeal-r:CoeqSolutions {h} (incl P) i =
--       let P₀ : f ⋆ (h ⋆ i) ∼ g ⋆ (h ⋆ i)
--           P₀ = f ⋆ (h ⋆ i)   ⟨ assoc-r-⋆ ⟩-∼
--                 (f ⋆ h) ⋆ i   ⟨ P ≀⋆≀ refl ⟩-∼
--                 (g ⋆ h) ⋆ i   ⟨ assoc-l-⋆ ⟩-∼
--                 g ⋆ (h ⋆ i)   ∎
--       in incl P₀
--     isIdeal-r.ideal-◍ isIdeal-r:CoeqSolutions = incl (absorb-r-⋆ ∙ absorb-r-⋆ ⁻¹)
-- -- private
-- module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory {𝑖} 𝒞}} where
--   Pair : (a b : 𝒞) -> 𝒰 _
--   Pair a x = Hom a x ×-𝒰 Hom a x

IxC : (𝒞 : Category 𝑖) -> 𝒰 _
IxC 𝒞 = ∑ λ (a : ⟨ 𝒞 ⟩) -> ∑ λ b -> HomPair a b

-- module _ (𝒞 : Category 𝑖) {{_ : isSizedCategory 𝒞}} where
--   𝓘C : (i : IxC 𝒞) -> Idealᵣ {𝒞 = Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} (incl (fst (snd i)))
--   𝓘C (_ , _ , f , g) = asIdealᵣ (f , g)
  -- ′ (CoeqSolutions (arrow f) (arrow g)) ′

-- module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑘} 𝒞}} {{_ : isDiscrete 𝒞}} {{_ : isSet-Str 𝒞}} where
  -- data isPrincipalC {a b : 𝒞} (f g : a ⟶ b) : 𝒰 𝑖 where
  --   solved : hasCoequalizer f g
  --   field princobj : 




module _ (𝒞 : SizedCategory 𝑖) where
  record isSplittableC (n : ℕ) {a b : ⟨ 𝒞 ⟩} (f : (a ⟶ b) ^ 2) : 𝒰 𝑖 where
    field famC : Fin-R n -> ∑ λ a' -> (HomPair a' b)
    field coversC : ∀{x} -> (h : b ⟶ x) -> (f ⌄ 0 ◆ h ∼ f ⌄ 1 ◆ h) ↔ (∀ p -> (famC p .snd) ⌄ 0 ◆ h ∼ (famC p .snd) ⌄ 1 ◆ h)
    -- field coversC : ⋀-fin (λ i -> 𝓘C 𝒞 (famC i)) ∼ 𝓘C 𝒞 i
    field fampropsC : ∀ k -> sizeC (famC k .snd) ≪ sizeC f
    -- P (_ , _ , f) (_ , _ , famC k .snd)
  open isSplittableC public

record isPrincipalFamilyCat (𝒞 : SizedCategory 𝑖) : 𝒰 (𝑖 ⁺) where
  field isBase : ∀{a x : ⟨ 𝒞 ⟩} -> (HomPair a x) -> 𝒰 (𝑖 ⌄ 1)
  field ∂C : ∀{x y : ⟨ 𝒞 ⟩} -> (i : HomPair x y)
           -> (isBase i +-𝒰 (∑ λ n -> isSplittableC 𝒞 n i))
  field isPrincipalC:Base : ∀{a b : ⟨ 𝒞 ⟩} -> ∀(f g : a ⟶ b) -> isBase (f , g) -> hasSizedCoequalizerDecision (f , g)

open isPrincipalFamilyCat {{...}} public

module _ {𝒞 : Category 𝑖}
         {{SP : isSizedCategory 𝒞}}
         {{_ : isPrincipalFamilyCat ′ ⟨ 𝒞 ⟩ ′}} where

  private
    Ix : ∀(a : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞) -> 𝒰 _
    Ix (incl x) = Bool +-𝒰 (∑ λ (a : ⟨ 𝒞 ⟩) -> HomPair a x)

    Bx : ∀(a : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞) -> 𝒰 _
    Bx (incl x) = Bool +-𝒰 (∑ λ (a : ⟨ 𝒞 ⟩) -> ∑ isBase {a = a} {x})

    𝒷' : ∀{a} -> Bx a -> Ix a
    𝒷' (left x) = left x
    𝒷' (just (x , (f , g) , p)) = just (x , (f , g))

    𝓘' : ∀{a} -> Ix a -> Idealᵣ a
    𝓘' (left false) = ⊥-Idealᵣ
    𝓘' (left true) = ⊤-Idealᵣ
    𝓘' (just (_ , (f , g))) = asIdealᵣ (f , g)

    Size' : WFT (ℓ₀ , ℓ₀)
    Size' = Lexi ⟨ SizeO {{SP}} ⟩ ⟨ SizeC {{SP}} ⟩

    size' : ∀{a} -> Ix a -> ⟨ Size' ⟩
    size' {a} (left x) = ⊥-WFT
    size' {a} (just (x , (f , g))) = sizeO a , sizeC (f , g)

  instance
    hasSizedFamily:byIsPrincipalFamilyCat : hasSizedFamily _ ′(Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)′
    hasSizedFamily:byIsPrincipalFamilyCat = record
      { Base = Bx
      ; Ind = Ix
      ; 𝒷 = 𝒷'
      ; 𝓘 = 𝓘'
      ; Size = Size'
      ; size = size'
      }

  private
    inv : {a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} → a ⟶ b → Ix a → Ix b
    inv (zero) _ = left true
    inv (some h) (left x) = left x
    inv (some h) (just (x , (f , g))) = just (x , (f ◆ h , g ◆ h))

    size-inv : {a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} (g : a ⟶ b) -> isGood g -> (i : Ix a) → size' (inv g i) ⪣ size' i
    size-inv (some x) good (left y) = left refl-≣
    size-inv (some x) (left ()) (just x₁)
    size-inv (some .(isCategory.id (_:&_.of 𝒞))) (just (left incl)) (just (_ , (f , g))) = left (cong₂-Str _,_ refl-≣ (cong-sizeC (f ◆ id , g ◆ id) (f , g) (unit-r-◆ , unit-r-◆)))
    size-inv (some x) (just (just good)) (just x₁) = right (first good)
    size-inv zero good i = initial-⊥-WFT

    lem-1 : {a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} {g : a ⟶ b} {i : Ix a} → 𝓘' (inv g i) ∼-Idealᵣ (g ⁻¹↷ 𝓘' i)
    lem-1 {a} {b} {zero} {left false} = antisym P terminal-⊤
      where
        P : ⊤ ≤ (zero ⁻¹↷ ⊥-Idealᵣ)
        ⟨ P ⟩ f x = incl (incl refl)
    lem-1 {a} {b} {zero} {left true} = antisym P terminal-⊤
      where
        P : ⊤ ≤ (zero ⁻¹↷ ⊤)
        ⟨ P ⟩ f x = incl tt
    lem-1 {a} {b} {zero} {just (_ , (f , g))} = antisym P terminal-⊤
      where
        P : ⊤ ≤ (zero ⁻¹↷ asIdealᵣ (f , g))
        P = incl (λ f₁ x → incl ideal-pt)
    lem-1 {a} {b} {some x} {left false} = antisym initial-⊥-Idealᵣ P
      where
        P : (some x ⁻¹↷ ⊥-Idealᵣ) ≤ ⊥-Idealᵣ
        ⟨ P ⟩ zero x = ideal-pt
    lem-1 {a} {b} {some x} {left true} = antisym P terminal-⊤
      where
        P : ⊤ ≤ (some x ⁻¹↷ ⊤)
        P = incl (λ f x₁ → incl tt)
    lem-1 {a} {b} {some x} {just (_ , (f , g))} = antisym P Q
      where
        P : asIdealᵣ (f ◆ x , g ◆ x) ≤ (some x ⁻¹↷ asIdealᵣ (f , g))
        P = incl (λ f₁ (incl p) → incl (incl (assoc-r-◆ ∙ p ∙ assoc-l-◆)))

        Q : (some x ⁻¹↷ asIdealᵣ (f , g)) ≤ asIdealᵣ (f ◆ x , g ◆ x)
        Q = incl (λ f₁ (incl (incl p)) → incl (assoc-l-◆ ∙ p ∙ assoc-r-◆))

    lem-2 : {a : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} (b : Bx a) → isEpiPrincipalᵣ (𝓘' (𝒷' b))
    lem-2 (left false) = isEpiPrincipalᵣ:⊥
    lem-2 (left true) = isEpiPrincipalᵣ:⊤
    lem-2 (just (x , (f , g) , isbase)) = Forward (isPrincipalC:Base f g isbase)

    lem-3 : ∀{a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> isSplittableC ′ ⟨ 𝒞 ⟩ ′ n (f , g)
          -> isSplittable n (right (_ , (f , g)))
    lem-3 {n} {a} {b} {f} {g} S = record
      { fam = fam'
      ; covers = antisym covers₀ covers₁
      ; famprops = λ k → second (fampropsC S k)
      }
      where
        fam' : Fin-R n → Ix (incl b)
        fam' i = right (famC S i)

        covers₀ : ⋀-fin (λ i → asIdealᵣ (fst (snd (famC S i)) , snd (snd (famC S i))))
                  ≤ asIdealᵣ (f , g)
        ⟨ covers₀ ⟩ zero h∈P = ideal-pt
        ⟨ covers₀ ⟩ (some h) h∈P = incl (some (coversC S (h) .snd Q))
          where
            Q : ∀(i : Fin-R n) -> (fst (snd (famC S i)) ◆ h) ∼ (snd (snd (famC S i)) ◆ h)
            Q i with ⟨ §-∧-Idealᵣ.prop-1 h∈P i ⟩
            ... | some p = p

        covers₁ : asIdealᵣ (f , g)
                  ≤ ⋀-fin (λ i → asIdealᵣ (fst (snd (famC S i)) , snd (snd (famC S i))))
        ⟨ covers₁ ⟩ zero h∈P = §-∧-Idealᵣ.prop-3 {P = (λ i → asIdealᵣ (fst (snd (famC S i)) , snd (snd (famC S i))))}
        ⟨ covers₁ ⟩ (some h) (incl (some h∈P)) = §-∧-Idealᵣ.prop-2 {P = λ i → asIdealᵣ (fst (snd (famC S i)) , snd (snd (famC S i)))} λ i → incl (some (coversC S h .fst h∈P i))

    lem-4 : {a : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} (i : Ix a) →
            (∑ (λ b → 𝓘' (𝒷' b) ∼-Idealᵣ 𝓘' i)) +-𝒰
            (∑ (λ n → isSplittable n i))
    lem-4 (left x) = left (left x , refl)
    lem-4 (just (x , (f , g))) with ∂C (f , g)
    ... | left isbase:fg = left ((right (x , (f , g) , isbase:fg)) , refl)
    ... | just (n , splittable) = right (n , lem-3 splittable)

  instance
    hasPrincipalFamily:byIsPrincipalFamilyCat : hasPrincipalFamily ′(Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)′
    hasPrincipalFamily:byIsPrincipalFamilyCat = record
                                                  { _⁻¹*_ = inv
                                                  ; size:⁻¹* = size-inv
                                                  ; preserves-𝓘:⁻¹* = lem-1
                                                  ; principalBase = lem-2
                                                  ; ∂ = lem-4
                                                  }




