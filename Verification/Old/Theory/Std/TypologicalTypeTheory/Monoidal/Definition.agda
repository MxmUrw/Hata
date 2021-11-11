
module Verification.Core.Theory.Std.TypologicalTypeTheory.Monoidal.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Core.Theory.Std.Specific.MetaTermCalculus.Definition
-- open import Verification.Core.Theory.Std.Specific.MetaTermCalculus.Instance.LogicalFramework
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.Monoidal
open import Verification.Core.Data.Type.Definition
open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation

open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Sum.Instance.Monad

-- module _ {{Types : hasJudgements {_} (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))}} where
--   myTest : CwJ _
--   myTest = 𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺)


module _ {K : Kinding 𝑖} (f : ⟨ K ⟩ -> 𝒰 𝑗) (inst : ∀{k} -> f (∂ₖ k) -> f k) where

  varProj-𝐔𝐧𝐢𝐯 : ∀{Γ : List ⟨ K ⟩} -> ∀{a} -> Γ ⊨-var a → rec-List f Γ -> rec-List f Γ ⊗ f a
  varProj-𝐔𝐧𝐢𝐯 zero (a , as) = (a , as) , a
  varProj-𝐔𝐧𝐢𝐯 (suc x) (a , as) = let (p , r) = varProj-𝐔𝐧𝐢𝐯 x as
                                  in (a , p) , r

  isCwJ:𝐓𝐲𝐩𝐞' : isCwJ K (𝐓𝐲𝐩𝐞' 𝑗)
  isCwJ.⊦ isCwJ:𝐓𝐲𝐩𝐞'       = λ a -> lift (f a)
  isCwJ.varTake isCwJ:𝐓𝐲𝐩𝐞' = incl $ λ (g , a) → inst a , g
  isCwJ.varProj isCwJ:𝐓𝐲𝐩𝐞' = PP
    where
      PP : ∀{Γ : List ⟨ K ⟩} -> ∀{a} -> Γ ⊨-var a →
              Hom-Lift (𝑗 , ℓ-suc 𝑗 , ℓ-suc 𝑗) (λ A B → A → B)
              (rec-List (λ a₁ → lift (f a₁)) Γ)
              (lift (Σ (lower (rec-List (λ a₁ → lift (f a₁)) Γ)) (λ a₁ → f a)))
      PP zero = incl λ (a , as) -> (a , as) , a
      PP (suc x) = incl λ (a , as) -> let (p , r) = ⟨ PP x ⟩ as
                                      in (a , p) , r

  isCwJ.diag isCwJ:𝐓𝐲𝐩𝐞'    = incl λ a -> a , a
  isCwJ.braid isCwJ:𝐓𝐲𝐩𝐞'   = incl λ (a , b) -> b , a

macro
  𝐔𝐧𝐢𝐯-𝒯ype : ∀ 𝑖 -> SomeStructure
  𝐔𝐧𝐢𝐯-𝒯ype 𝑖 = #structureOn (Kleisli {𝒞 = 𝐔𝐧𝐢𝐯 𝑖} (⊤-𝒰 {𝑖} +⧿))

module _ {K : Kinding 𝑖} (f : ⟨ K ⟩ -> 𝒰 𝑗) (inst : ∀{k} -> f (∂ₖ k) -> f k) where


  isCwJ:𝐔𝐧𝐢𝐯-𝒯ype : isCwJ K (𝐔𝐧𝐢𝐯-𝒯ype 𝑗)
  isCwJ.⊦ isCwJ:𝐔𝐧𝐢𝐯-𝒯ype = λ x → incl (f x)
  isCwJ.varTake isCwJ:𝐔𝐧𝐢𝐯-𝒯ype = incl (λ (g , a) → right (inst a , g))
  isCwJ.varProj isCwJ:𝐔𝐧𝐢𝐯-𝒯ype = PP
    where
      PP : ∀{Γ : List ⟨ K ⟩} -> ∀{a} -> Γ ⊨-var a →
          Hom-Base (λ x y → Kleisli.⟨ x ⟩ → ⊤-𝒰 +-𝒰 Kleisli.⟨ y ⟩)
          (rec-List (λ x → incl (f x)) Γ)
          (incl (Σ Kleisli.⟨ rec-List (λ x → incl (f x)) Γ ⟩ (λ a₁ → f a)))
      PP zero = incl (λ (a , as) → right ((a , as) , a))
      PP (suc x) = incl (λ (a , as) → (do (p , r) <- ⟨ PP x ⟩ as
                                          return ((a , p) , r)))
  isCwJ.diag isCwJ:𝐔𝐧𝐢𝐯-𝒯ype = incl (λ x -> right (x , x))
  isCwJ.braid isCwJ:𝐔𝐧𝐢𝐯-𝒯ype = incl (λ (a , b) → right (b , a))

  TheCwJ : CwJ K _
  TheCwJ = (Kleisli {𝒞 = 𝐔𝐧𝐢𝐯 𝑗} _) since isCwJ:𝐔𝐧𝐢𝐯-𝒯ype
-- (⊤-𝒰 {𝑗} +⧿)




module _ (K : Kinding 𝑖) where
  record TypeTheory-⊗ 𝑗 𝑘 : 𝒰 (𝑖 ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
    field 𝒯erm : CwJ K 𝑗
    field 𝒯ype : CwJ K 𝑘
    field typing : Functor ′ ⟨ 𝒯erm ⟩ ′ ′ ⟨ 𝒯ype ⟩ ′

  open TypeTheory-⊗ {{...}} public

  -- field 𝒯erm : CwJ (𝑗 ⁺ , 𝑗 ⁺ , 𝑗 ⁺ , 𝑗 ⁺)
  -- field {{Types}} : hasJudgements {_} (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))
  -- field typing : 𝒯erm ⟶ (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))





