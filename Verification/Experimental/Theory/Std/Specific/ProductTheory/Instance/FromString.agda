
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Function.Surjective
open import Verification.Experimental.Data.Nat.Free
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
open import Verification.Experimental.Data.Substitution.Variant.Base.Definition
open import Verification.Experimental.Data.Substitution.Property.Base
open import Verification.Experimental.Theory.Std.Presentation.AnnGraph.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition

ι-Fin-R : Fin-R n -> ℕ
ι-Fin-R zero = zero
ι-Fin-R (suc m) = suc (ι-Fin-R m)

instance
  IShow:Fin-R : IShow (Fin-R n)
  IShow:Fin-R = record { show = λ x → show (ι-Fin-R x) }

UntypedCon : ProductTheory 𝑖 -> 𝒰 _
UntypedCon 𝒯 = ∑ λ xs -> ∑ λ x -> Con 𝒯 xs x


module _ (𝒯 : ProductTheory ℓ₀) {{_ : IShow (Sort 𝒯)}} where
  data SortTermᵈ (n : 人ℕ) : 𝒰₀ where
    var : [ n ]ᶠ -> SortTermᵈ n
    con : Sort 𝒯 -> SortTermᵈ n

  SortTermᵘ : 𝐅𝐢𝐧𝐈𝐱 (⊤-𝒰 {ℓ₀}) -> 𝐈𝐱 (⊤-𝒰 {ℓ₀}) (𝐔𝐧𝐢𝐯 ℓ₀)
  SortTermᵘ a = indexed (λ _ → SortTermᵈ ⟨ a ⟩)

  macro SortTerm = #structureOn SortTermᵘ

  instance
    isFunctor:SortTerm : isFunctor (𝐅𝐢𝐧𝐈𝐱 ⊤-𝒰) (𝐈𝐱 ⊤-𝒰 (𝐔𝐧𝐢𝐯 ℓ₀)) SortTerm
    isFunctor.map isFunctor:SortTerm = {!!}
    isFunctor.isSetoidHom:map isFunctor:SortTerm = {!!}
    isFunctor.functoriality-id isFunctor:SortTerm = {!!}
    isFunctor.functoriality-◆ isFunctor:SortTerm = {!!}

  instance
    isRelativeMonad:SortTerm : isRelativeMonad (𝑓𝑖𝑛 ⊤-𝒰) SortTerm
    isRelativeMonad.repure isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reext isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reunit-l isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reassoc isRelativeMonad:SortTerm = {!!}

  module §-SortTerm where
    prop-1 : ∀{n : 人ℕ} -> n ∼ ◌ -> SortTermᵈ n -> Sort 𝒯
    prop-1 {n} n∼◌ (var (a , x)) = impossible p4
      where
        p1 : el n ≅ el ◌
        p1 = cong-∼ n∼◌

        p2 : ix (el n) a
        p2 = x

        p3 : ix (el ◌) a
        p3 = ⟨ p1 ⟩ a p2

        p4 : 𝟘-𝒰
        p4 with p3
        ... | ()

    prop-1 {n} n∼◌ (con x) = x

    prop-2 : ∀{m n : 人ℕ} -> n ∼ ◌ -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (m ⋆ incl tt)) (incl n) -> 人List (Sort 𝒯) × Sort 𝒯
    prop-2 n∼◌ (f ⋆-⧜ incl x) = map (prop-1 n∼◌) f' , (prop-1 n∼◌ x)
      where
        f' = §-⧜𝐒𝐮𝐛𝐬𝐭-⊤.prop-1 {T = SortTerm} (f)

  private
    macro
      ℬ : SomeStructure
      ℬ = #structureOn (InductiveSubstitution SortTerm)

    l' : UntypedCon 𝒯 -> ℕ
    l' (τs , τ , _) = length τs


    Edge : ∀{n : 人ℕ} -> (r : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> 𝒰 _
    Edge r = ∑ λ s -> ∑ λ t -> TreePath r s ×-𝒰 TreeStep s t

    Vertex : ∀{n : 人ℕ} -> (r : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> 𝒰 _
    Vertex r = ∑ TreePath r


    F : 人ℕ -> Functor ℬ (𝐔𝐧𝐢𝐯 ℓ₀)
    F n = f since {!!}
      where
        f : ℬ -> 𝐔𝐧𝐢𝐯 ℓ₀
        f b = (incl (n ⋆ incl tt) ⟶ b)

    module _ {n : 人ℕ} where
      bo-impl : (t : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> ℬ
      bo-impl t = incl n

      bo' : {t : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l'} -> Vertex t -> ℬ
      bo' (t' , v) = bo-impl t'

      get-con-head-boundary : (t : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> ⟨ F n ⟩ (incl n)
      get-con-head-boundary (node (τs , τ , x) x₁) = ⦗ id , ⧜subst (incl (con τ)) ⦘
      get-con-head-boundary (var x) = ⦗ id , ⧜subst (incl (var x)) ⦘

      get-con-branch-boundary : {t s : VecTree (UntypedCon 𝒯) [ n ]ᶠ l'} (e : TreeStep t s) -> ⟨ F n ⟩ (incl n)
      get-con-branch-boundary {(node (τs , τ , c) ts)} {s} (incl ts .s i x) = ⦗ id , ⧜subst (incl (con (lookup' τs i))) ⦘

    module _ {n : 人ℕ} {t : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l'} where
      source' : Edge t -> ∑ λ (v : Vertex t) -> ⟨ F n ⟩ (bo' v)
      source' (t₁ , t₂ , _ , _) = (t₂ , {!!}) , get-con-head-boundary t₂

      target' : Edge t -> ∑ λ (v : Vertex t) -> ⟨ F n ⟩ (bo' v)
      target' (t₁ , t₂ , p₀₁ , e₁₂) = (t₁ , p₀₁) , get-con-branch-boundary e₁₂

  makeInitialGraph : ∀{n} -> (t : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> AnnGraph (F n) (Edge t)
  makeInitialGraph {n} t = Vertex t since P
    where
      P : isAnnGraph (F n) (Edge t) (Vertex t)
      isAnnGraph.bo P = bo'
      isAnnGraph.source P = source'
      isAnnGraph.target P = target'
  private
    ℐ = makeInitialGraph

  isConnected:InitialGraph : ∀{n} -> (t : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> isConnected (ℐ t)
  isConnected:InitialGraph t a b = trans-UPath (sym-UPath p0) p1
    where
      v₀ : ⟨ ℐ t ⟩
      v₀ = t , []

      p0 : UPath (ℐ t) v₀ a
      p0 = {!!}

      p1 : UPath (ℐ t) v₀ b
      p1 = {!!}

  module _ {n} (t : VecTree (UntypedCon 𝒯) [ n ]ᶠ l')
               (𝒢 : AnnGraph (F n) (Edge t))
               (𝒢P : isContracted 𝒢)
               (h : AnnHom (ℐ t) 𝒢)
               (isSurjective:h : isSurjective-𝒰 ⟨ h ⟩)
               where

    private
      instance _ = isSurjective:h

      v₀ : ⟨ ℐ t ⟩
      v₀ = t , []

      w₀ : ⟨ 𝒢 ⟩
      w₀ = ⟨ h ⟩ v₀

      isConnected:𝒢 : isConnected 𝒢
      isConnected:𝒢 = §-AnnGraph.prop-1 h (isConnected:InitialGraph t)

      isContr:𝒢 : ∀{w : ⟨ 𝒢 ⟩} -> w ≡ w₀
      isContr:𝒢 = §-AnnGraph.prop-3 (isConnected:𝒢) (𝒢P) _ _

      lem-1 : ∀{w : ⟨ 𝒢 ⟩} -> bo w ≡ bo w₀
      lem-1 = cong bo (isContr:𝒢)

      module _ (isGood:w₀ : bo w₀ ≅ ⊥) where
        τctx : ∀{s1 s2 : VecTree (UntypedCon 𝒯) [ n ]ᶠ l'} -> TreePath t s1 -> TreeStep s1 s2 -> 人List (Sort 𝒯) × Sort 𝒯
        τctx {x} p1 p2 = §-SortTerm.prop-2 {!!} ⟨ X .snd ⟩
          where
            X : ∑ λ (v : ⟨ 𝒢 ⟩) -> ⟨ F n ⟩ (bo v)
            X = target (_ , {!!} , p1 , p2)

        myType : 人List (Sort 𝒯) × Sort 𝒯 -> 𝒰 _
        myType (τs , τ) = Term₁-𝕋× 𝒯 τs τ

        lem-x : ∀{s1 s2 : VecTree (UntypedCon 𝒯) [ n ]ᶠ l'} -> (p : TreePath t s1) -> (q : TreeStep s1 s2) -> myType (τctx p q)
        lem-x {s1} {node (αs , α , c) x} p q = con {!!} {!!}
        lem-x {s1} {var x} p q = var {!!}


          -- p : TreePath t v
          -- p = ?

    -- makeTerm : Term₁-𝕋× 𝒯
    -- makeTerm = ?

--   mutual
--     parseTokenTrees : ∀{n} -> List (Tree (UntypedCon 𝒯) (Fin-R n)) -> (τs : List (Sort 𝒯)) -> String +-𝒰 (∑ λ xs -> Terms-𝕋× 𝒯 (incl (ι τs)) xs)
--     parseTokenTrees ⦋⦌ ⦋⦌ = right (incl ◌ , ◌-⧜)
--     parseTokenTrees ⦋⦌ (x ∷ ss) = left $ "wrong number of args!"
--     parseTokenTrees (x ∷ ts) ⦋⦌ = left $ "wrong number of args!"
--     parseTokenTrees (t ∷ ts) (s ∷ ss) with parseTokenTree t s | parseTokenTrees ts ss
--     ... | left x | left y = left $ x <> " & " <> y
--     ... | left x | just x₁ = left $ x
--     ... | just x | left y = left y
--     ... | just (◌-⧜ , x) | just (incl ◌-⧜ , y) = right (_ , (incl x ⋆-⧜ y))
--     ... | _ | _ = left $ "did not expect variables"

--     parseTokenTree : ∀{n} -> Tree (UntypedCon 𝒯) (Fin-R n) -> (τ : Sort 𝒯) -> String +-𝒰 (∑ λ xs -> Term₁-𝕋× 𝒯 xs τ)
--     parseTokenTree (node (ys , y , x) xs) s with y ≟-Str s
--     ... | no ¬p = left $ "kind mismatch: " <> show s <> " ≠ " <> show y
--     ... | yes refl-≣ with parseTokenTrees xs ys
--     ... | left err = left err
--     ... | just (xs , ts) = right (⟨ xs ⟩ , con x ts)
--     parseTokenTree (var x) s = left $ "unexpected var " <> show x

--   inferTokenTree : ∀{n} -> Tree (UntypedCon 𝒯) (Fin-R n) -> String +-𝒰 (∑ λ xs -> ∑ λ x -> Term₁-𝕋× 𝒯 xs x)
--   inferTokenTree (node (_ , τ , x) xs) = map (λ (xs , y) → (xs , _ , y)) (parseTokenTree (node (_ , _ , x) xs) τ)
--   inferTokenTree (var x) = left $ "unexpected var " <> show x



-- module _ {𝒯 : ProductTheory ℓ₀} {{_ : IShow (Sort 𝒯)}} {{Def : TokenDefinition (UntypedCon 𝒯)}} where
--   private
--     getTerm : Tree (UntypedCon 𝒯) (String) -> String +-𝒰 (∑ λ xs -> ∑ λ x -> Term₁-𝕋× (𝒯) xs x)
--     getTerm t with renameFreeVariables (0 , emptyC) t
--     ... | uc , t with finitizeFreeVariables uc t
--     ... | left err = left "Could not finitize free vars"
--     ... | just t with inferTokenTree 𝒯 t
--     ... | left err = left err
--     ... | right x = right x

--     𝑹 = (∑ λ xs -> ∑ λ x -> Term₁-𝕋× (𝒯) xs x)

--     getTerms : String -> String +-𝒰 (𝑹 ^ 2)
--     getTerms s = do
--       (t1 , t2) <- parseTwolines Def s
--       r1 <- getTerm t1
--       r2 <- getTerm t2
--       return (r1 , r2)

--   instance
--     fromString:ProductTheory : FromString (∑ λ xs -> ∑ λ x -> Term₁-𝕋× 𝒯 xs x)
--     fromString:ProductTheory = record { fromString = λ s -> parseTokens Def s >>= getTerm }

--   instance
--     fromString:ProductTheory2 : FromString (𝑹 ^ 2)
--     fromString:ProductTheory2 = record { fromString = getTerms }

--   private
--     mutual
--       lem-10s : ∀{xs} {x} -> (Terms-𝕋× 𝒯 xs x) -> String
--       lem-10s ◌-⧜ = ""
--       lem-10s (incl x) = " " <> lem-10 x
--       lem-10s (t ⋆-⧜ s) = lem-10s t <> lem-10s s

--       lem-10 : ∀{xs} {x} -> (Term₁-𝕋× 𝒯 xs x) -> String
--       lem-10 (var x) = "var"
--       lem-10 (con c x) = "(" <> TokenDefinition.name Def (_ , _ , c) <> lem-10s x <> ")"

--   instance
--     IShow:Term-𝕋× : ∀{xs} {x} -> IShow (Term₁-𝕋× 𝒯 xs x)
--     IShow:Term-𝕋× = record { show = lem-10 }

