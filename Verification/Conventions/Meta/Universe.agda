
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Meta.Universe where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta.Term


try-unify-𝔏n : Term -> ℕ -> TC ℕ
try-unify-𝔏n hole n =
  do target-Type <- quoteTC (𝔏 ^ n)
     -- target-Type <- normalise target-Type
     _ <- unify hole target-Type
     return n

try-eq-𝔏n : Term -> ℕ -> TC ℕ
try-eq-𝔏n hole n =
  do `cmp` <- quoteTC (𝔏 ^ n)
     `cmp` <- normalise `cmp`
     if (`cmp` ≟ hole) then (return n) else (printErr (show `cmp` <> "\nis not eq to\n" <> show hole))


try-all : ∀{a : 𝒰' 𝑖} -> ℕ -> (ℕ -> TC a) -> TC a
try-all zero f = noConstraints (f zero)
try-all (suc n) f = catchTC (noConstraints (f (suc n))) (try-all n f)



macro
  𝔘2 : Term -> Term -> TC 𝟙-𝒰
  𝔘2 level-Term hole-Term = do
      level-Type <- inferType level-Term
      `𝔏` <- quoteTC 𝔏
      `ℕ` <- quoteTC ℕ
      -- `𝒰''` <- quoteωTC 𝒰''

      let try-simple = (
            do
              n <- try-all 0 (try-unify-𝔏n level-Type)
              target-Type <- quoteTC (𝔏 ^ n)
              target-Type <- normalise target-Type
              unify level-Type target-Type

              level <- assertType (𝔏 ^ n) $ unquoteTC level-Term
              checkType level-Term `ℕ`

              `𝒰` <- quoteTC (𝒰' (merge level))
              unify hole-Term `𝒰`)

      -- try-simple
      -- let otherwise = printErr "Could not find universe type"
      -- level-Type <- catchTC try-simple otherwise

      level <- unquoteTC level-Term

      final-Type <- quoteTC (𝒰' level)

      res <- checkType final-Type `ℕ`
      unify hole-Term res

      return tt

postulate
  ls : 𝔏 ^ 10


#merge : ∀{A : 𝒰' 𝑖} -> Term -> TC 𝟙-𝒰
#merge {A = A} hole =
  do
     `A` <- quoteTC A
     `A` <- normalise `A`

     let dofirst =
          do n <- try-all 5 (try-eq-𝔏n `A`)
             fun <- quoteTC (λ (ls : 𝔏 ^ n) -> (merge ls))
             unify hole fun

     let otherwise =
          do res <- quoteTC (λ (a : A) -> a)
             unify hole res

     catchTC dofirst otherwise



𝒰 : ∀{A : 𝒰' 𝑖} -> (a : A) -> {@(tactic #merge {A = A}) f : A -> 𝔏} -> 𝒰' (f a ⁺')
𝒰 a {f = f} = 𝒰' (f a)

𝒰₀ = 𝒰' ℓ₀
𝒰₁ = 𝒰' ℓ₁
𝒰₂ = 𝒰' ℓ₂


-- test : 𝒰 (ls ⌄ 7)
-- test = {!!}

