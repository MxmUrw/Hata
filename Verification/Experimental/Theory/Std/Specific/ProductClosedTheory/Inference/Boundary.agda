
module Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Computation.Unification.Definition
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString3
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem
open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Module

open import Verification.Experimental.Data.Expr.Variant.Base.InferenceTask
open import Verification.Experimental.Data.Expr.Variant.Base.Definition
open import Verification.Experimental.Data.SyntaxTree.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries


data 𝒷₀ : 𝒰₀ where
  分tyᵗ 全tyᵗ jdgᵗ : 𝒷₀


private
  lem-2 : (a b : 𝒷₀) → Decision (a ≡-Str b)
  lem-2 分tyᵗ 分tyᵗ = yes refl-≣
  lem-2 分tyᵗ 全tyᵗ = no (λ ())
  lem-2 分tyᵗ jdgᵗ = no (λ ())
  lem-2 全tyᵗ 分tyᵗ = no (λ ())
  lem-2 全tyᵗ 全tyᵗ = yes refl-≣
  lem-2 全tyᵗ jdgᵗ = no (λ ())
  lem-2 jdgᵗ 分tyᵗ = no (λ ())
  lem-2 jdgᵗ 全tyᵗ = no (λ ())
  lem-2 jdgᵗ jdgᵗ = yes refl-≣

instance
  isDiscrete:𝒷₀ : isDiscrete 𝒷₀
  isDiscrete:𝒷₀ = record { _≟-Str_ = lem-2 }

data 𝒷₁ : List 𝒷₀ → 𝒷₀ → 𝒰 ℓ₀ where
  ⇒ᵗ : 𝒷₁ (分tyᵗ ∷ 分tyᵗ ∷ []) 分tyᵗ
  ℕᵗ : 𝒷₁ [] 分tyᵗ
  𝔹ᵗ : 𝒷₁ [] 分tyᵗ
  []ᵗ : 𝒷₁ [] 全tyᵗ
  ▻ᵗ   : 𝒷₁ (全tyᵗ ∷ 分tyᵗ ∷ []) 全tyᵗ
  影⊢ᵗ : 𝒷₁ (全tyᵗ ∷ 分tyᵗ ∷ []) jdgᵗ
  分⊢ᵗ : 𝒷₁ (全tyᵗ ∷ 分tyᵗ ∷ []) jdgᵗ
  全⊢ᵗ : 𝒷₁ (全tyᵗ ∷ 分tyᵗ ∷ []) jdgᵗ

private
  lem-1 : ∀{xs : List 𝒷₀} {x : 𝒷₀} -> (a b : 𝒷₁ xs x) -> Decision (a ≣ b)
  lem-1 ⇒ᵗ ⇒ᵗ = yes refl-≣
  lem-1 ℕᵗ ℕᵗ = yes refl-≣
  lem-1 ℕᵗ 𝔹ᵗ = no (λ ())
  lem-1 𝔹ᵗ ℕᵗ = no (λ ())
  lem-1 𝔹ᵗ 𝔹ᵗ = yes refl-≣
  lem-1 []ᵗ []ᵗ = yes refl-≣
  lem-1 ▻ᵗ ▻ᵗ = yes refl-≣
  lem-1 影⊢ᵗ 影⊢ᵗ = yes refl-≣
  lem-1 影⊢ᵗ 分⊢ᵗ = no (λ ())
  lem-1 影⊢ᵗ 全⊢ᵗ = no (λ ())
  lem-1 分⊢ᵗ 影⊢ᵗ = no (λ ())
  lem-1 分⊢ᵗ 分⊢ᵗ = yes refl-≣
  lem-1 分⊢ᵗ 全⊢ᵗ = no (λ ())
  lem-1 全⊢ᵗ 影⊢ᵗ = no (λ ())
  lem-1 全⊢ᵗ 分⊢ᵗ = no (λ ())
  lem-1 全⊢ᵗ 全⊢ᵗ = yes refl-≣



𝒷 : 𝕋×.統.𝒜 ℓ₀
-- 𝒷 : 𝒜 ℓ₀
Sort 𝒷 = 𝒷₀
isDiscrete:Sort 𝒷 = it
isSet-Str:Sort 𝒷 = {!!}
Con 𝒷 = 𝒷₁
isDiscrete:Con 𝒷 = record { _≟-Str_ = lem-1 }

-- Sort 𝒷 = 𝒷₀
-- isDiscrete:Sort 𝒷 = it
-- isSet-Str:Sort 𝒷 = {!!}
-- Con 𝒷 = 𝒷₁
-- isDiscrete:Con 𝒷 = record { _≟-Str_ = lem-1 }

showTokType : (UntypedCon 𝒷) -> Text
showTokType (_ , _ , ⇒ᵗ) = "Arr"
showTokType (_ , _ , ℕᵗ) = "Nat"
showTokType (_ , _ , 𝔹ᵗ) = "Bool"
showTokType (_ , _ , []ᵗ) = "Nil"
showTokType (_ , _ , ▻ᵗ) = "Snoc"
showTokType (_ , _ , 影⊢ᵗ) = "Entails"
showTokType (_ , _ , 分⊢ᵗ) = "Entails"
showTokType (_ , _ , 全⊢ᵗ) = "Entails"

𝕋ΛTypeData : BaseExprData
TokenType 𝕋ΛTypeData = (UntypedCon 𝒷)
IShow:TokenType 𝕋ΛTypeData = record { show = showTokType }
hasElementNames:TokenType 𝕋ΛTypeData = record
  { all =
    (_ , _ , 𝔹ᵗ)
    ∷ (_ , _ , ℕᵗ)
    ∷ (_ , _ , ⇒ᵗ)
    ∷ (_ , _ , ▻ᵗ)
    ∷ (_ , _ , []ᵗ)
    -- ∷ (_ , _ , 影⊢ᵗ)
    -- ∷ (_ , _ , 分⊢ᵗ)
    -- ∷ (_ , _ , 全⊢ᵗ)
    ∷ []
  ; name = showTokType
  }

𝕋ΛTypeData2 : SyntaxTreeData
TokenType 𝕋ΛTypeData2 = UntypedCon 𝒷
TokenSize 𝕋ΛTypeData2 = λ (τs , _ , x) → length τs


{-
Type-𝕋Λ : 𝒰₀
Type-𝕋Λ = Term₁-𝕋× 𝒷 ◌ tyᵗ

module _ where -- §-Type-𝕋Λ-Example where
  e1 : Type-𝕋Λ
  e1 = con ℕᵗ ◌-⧜

  e2 : Type-𝕋Λ
  e2 = con 𝔹ᵗ ◌-⧜

x = unify (⧜subst (incl e1)) (⧜subst (incl e2))

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  myfun : A +-𝒰 B -> Bool
  myfun (left a) = false
  myfun (right b) = true


instance
  tokdef : TokenDefinition (UntypedCon 𝒷)
  TokenDefinition.all tokdef =
    (_ , _ , 𝔹ᵗ)
    ∷ (_ , _ , ℕᵗ)
    ∷ (_ , _ , ⇒ᵗ)
    ∷ (_ , _ , ▻ᵗ)
    ∷ (_ , _ , []ᵗ)
    ∷ (_ , _ , ⊢ᵗ)
    ∷ []
  TokenDefinition.name tokdef (_ , _ , ⇒ᵗ) = "Arr"
  TokenDefinition.name tokdef (_ , _ , ℕᵗ) = "Nat"
  TokenDefinition.name tokdef (_ , _ , 𝔹ᵗ) = "Bool"
  TokenDefinition.name tokdef (_ , _ , []ᵗ) = "Nil"
  TokenDefinition.name tokdef (_ , _ , ▻ᵗ) = "Cons"
  TokenDefinition.name tokdef (_ , _ , ⊢ᵗ) = "Entails"

instance
  IShow:𝒷₀ : IShow (𝒷₀)
  IShow.show IShow:𝒷₀ tyᵗ = "Ty"
  IShow.show IShow:𝒷₀ 全tyᵗ = "Ctx"
  IShow.show IShow:𝒷₀ jdgᵗ = "Jdg"


-}

{-
𝑹' = 𝑹 {𝒯 =  𝒷}

dounify : 𝑹' -> 𝑹' -> String +-𝒰 𝑹'
dounify (τsx , τx , x) (τsy , τy , y) with τx ≟-Str τy
... | no _ = left "Wrong result kinds!"
... | yes refl-≣ = case unify fx' fy' of (λ x₁ → left "Could not unify!") λ _ → right (getArr (fx' ◆ π₌))
  where
      -- xa : ⧜𝐒𝐮𝐛𝐬𝐭 ′(Term-𝕋× 𝒷)′
      asx : 𝐂𝐭𝐱 (𝒷)
      asx = incl τsx
      ax : 𝐂𝐭𝐱 (𝒷)
      ax = incl (incl τx)
      fx : ax ⟶ asx
      fx = ⧜subst (incl x)

      asy : 𝐂𝐭𝐱 (𝒷)
      asy = incl τsy
      ay : 𝐂𝐭𝐱 (𝒷)
      ay = incl (incl τy)
      fy : ay ⟶ asy
      fy = ⧜subst (incl y)

      fx' : ax ⟶ asx ⊔ asy
      fx' = fx ◆ ι₀

      fy' : ay ⟶ asx ⊔ asy
      fy' = fy ◆ ι₁

      getArr : ∀{b} -> ax ⟶ b -> 𝑹'
      getArr (⧜subst (incl f)) = _ , (_ , f)


compareLambdaType : String -> String
compareLambdaType s with ProductTheory:fromString {𝒯 = 𝒷} s
... | left err = "Error " <> err
... | just ((_ , _ , x) , (_ , _ , y)) = "Got types: " <> show x <> " and " <> show y
                                         <> "\nthe unification is: " <> case res of (λ x -> x) (λ (_ , _ , a) -> show a)
      where
        res = dounify (_ , _ , x) (_ , _ , y)
-}
