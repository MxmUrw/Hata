
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Instance.Functor
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Sum.Instance.Monad
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Data.Substitution.Definition

ι-Fin-R : Fin-R n -> ℕ
ι-Fin-R zero = zero
ι-Fin-R (suc m) = suc (ι-Fin-R m)

instance
  IShow:Fin-R : IShow (Fin-R n)
  IShow:Fin-R = record { show = λ x → show (ι-Fin-R x) }

UntypedCon : ProductTheory 𝑖 -> 𝒰 _
UntypedCon 𝒯 = ∑ λ xs -> ∑ λ x -> Con 𝒯 xs x


module _ (𝒯 : ProductTheory ℓ₀) {{_ : IShow (Sort 𝒯)}} (Def : TokenDefinition (UntypedCon 𝒯)) where

  mutual
    parseTokenTrees : ∀{n} -> List (Tree (UntypedCon 𝒯) (Fin-R n)) -> (τs : List (Sort 𝒯)) -> String +-𝒰 (∑ λ xs -> Terms-𝕋× 𝒯 (incl (ι τs)) xs)
    parseTokenTrees ⦋⦌ ⦋⦌ = right (incl ◌ , ◌-⧜)
    parseTokenTrees ⦋⦌ (x ∷ ss) = left $ "wrong number of args!"
    parseTokenTrees (x ∷ ts) ⦋⦌ = left $ "wrong number of args!"
    parseTokenTrees (t ∷ ts) (s ∷ ss) with parseTokenTree t s | parseTokenTrees ts ss
    ... | left x | left y = left $ x <> " & " <> y
    ... | left x | just x₁ = left $ x
    ... | just x | left y = left y
    ... | just (◌-⧜ , x) | just (incl ◌-⧜ , y) = right (_ , (incl x ⋆-⧜ y))
    ... | _ | _ = left $ "did not expect variables"

    parseTokenTree : ∀{n} -> Tree (UntypedCon 𝒯) (Fin-R n) -> (τ : Sort 𝒯) -> String +-𝒰 (∑ λ xs -> Term₁-𝕋× 𝒯 xs τ)
    parseTokenTree (node (ys , y , x) xs) s with y ≟-Str s
    ... | no ¬p = left $ "kind mismatch: " <> show s <> " ≠ " <> show y
    ... | yes refl-≣ with parseTokenTrees xs ys
    ... | left err = left err
    ... | just (xs , ts) = right (⟨ xs ⟩ , con x ts)
    parseTokenTree (var x) s = left $ "unexpected var " <> show x

  inferTokenTree : ∀{n} -> Tree (UntypedCon 𝒯) (Fin-R n) -> String +-𝒰 (∑ λ xs -> ∑ λ x -> Term₁-𝕋× 𝒯 xs x)
  inferTokenTree (node (_ , τ , x) xs) = map (λ (xs , y) → (xs , _ , y)) (parseTokenTree (node (_ , _ , x) xs) τ)
  inferTokenTree (var x) = left $ "unexpected var " <> show x



module _ {𝒯 : ProductTheory ℓ₀} {{_ : IShow (Sort 𝒯)}} {{Def : TokenDefinition (UntypedCon 𝒯)}} where
  private
    getTerm : Tree (UntypedCon 𝒯) (String) -> String +-𝒰 (∑ λ xs -> ∑ λ x -> Term₁-𝕋× (𝒯) xs x)
    getTerm t with renameFreeVariables (0 , emptyC) t
    ... | uc , t with finitizeFreeVariables uc t
    ... | left err = left "Could not finitize free vars"
    ... | just t with inferTokenTree 𝒯 Def t
    ... | left err = left err
    ... | right x = right x

    𝑹 = (∑ λ xs -> ∑ λ x -> Term₁-𝕋× (𝒯) xs x)

    getTerms : String -> String +-𝒰 (𝑹 ^ 2)
    getTerms s = do
      (t1 , t2) <- parseTwolines Def s
      r1 <- getTerm t1
      r2 <- getTerm t2
      return (r1 , r2)

  instance
    fromString:ProductTheory : FromString (∑ λ xs -> ∑ λ x -> Term₁-𝕋× 𝒯 xs x)
    fromString:ProductTheory = record { fromString = λ s -> parseTokens Def s >>= getTerm }

  instance
    fromString:ProductTheory2 : FromString (𝑹 ^ 2)
    fromString:ProductTheory2 = record { fromString = getTerms }

  private
    mutual
      lem-10s : ∀{xs} {x} -> (Terms-𝕋× 𝒯 xs x) -> String
      lem-10s ◌-⧜ = ""
      lem-10s (incl x) = " " <> lem-10 x
      lem-10s (t ⋆-⧜ s) = lem-10s t <> lem-10s s

      lem-10 : ∀{xs} {x} -> (Term₁-𝕋× 𝒯 xs x) -> String
      lem-10 (var x) = "var"
      lem-10 (con c x) = "(" <> TokenDefinition.name Def (_ , _ , c) <> lem-10s x <> ")"

  instance
    IShow:Term-𝕋× : ∀{xs} {x} -> IShow (Term₁-𝕋× 𝒯 xs x)
    IShow:Term-𝕋× = record { show = lem-10 }


