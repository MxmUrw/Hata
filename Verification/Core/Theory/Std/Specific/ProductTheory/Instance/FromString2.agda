
module Verification.Core.Theory.Std.Specific.ProductTheory.Instance.FromString2 where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Function.Surjective
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Instance.Functor
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Sum.Instance.Monad
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Core.Theory.Std.Presentation.Token.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Substitution.Property.Base
open import Verification.Core.Theory.Std.Presentation.NGraph.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition

module _ {A : 𝒰 𝑖} {R : ⋆List A -> A -> 𝒰 𝑖} where
  π₀-⋆-⧜ : ∀{as0 as1 bs : ⋆List A} -> CtxHom R (as0 ⋆ as1) bs -> CtxHom R as0 bs
  π₀-⋆-⧜ (f ⋆-⧜ g) = f

  π₁-⋆-⧜ : ∀{as0 as1 bs : ⋆List A} -> CtxHom R (as0 ⋆ as1) bs -> CtxHom R as1 bs
  π₁-⋆-⧜ (f ⋆-⧜ g) = g


ι-Fin-R : Fin-R n -> ℕ
ι-Fin-R zero = zero
ι-Fin-R (suc m) = suc (ι-Fin-R m)

instance
  IShow:Fin-R : IShow (Fin-R n)
  IShow:Fin-R = record { show = λ x → show (ι-Fin-R x) }

UntypedCon : ProductTheory 𝑖 -> 𝒰 _
UntypedCon 𝒯 = ∑ λ xs -> ∑ λ x -> Con 𝒯 xs x


module _ (𝒯 : ProductTheory ℓ₀) {{_ : IShow (Sort 𝒯)}} where

  -----------------------------------------
  -- nodes of the NGraph
  data SubNode (n : 人ℕ) : 𝒰₀ where
    isNode : UntypedCon 𝒯 -> SubNode n
    isVar :  [ n ]ᶠ -> SubNode n

  l' : UntypedCon 𝒯 -> 人ℕ
  l' (τs , τ , _) = map (const tt) (ι τs)

  size' : ∀{n} -> SubNode n -> 人ℕ
  size' (isNode n) = l' n
  size' (isVar x) = ◌

  data Node (n : 人ℕ) : 𝒰₀ where
    isTop : Node n
    notTop : SubNode n -> Node n

  size : ∀{n} -> Node n -> 人ℕ
  size (notTop x) = incl tt ⋆ size' x
  size isTop = incl tt

  -----------------------------------------
  -- the category of sorts and substitutions

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

    prop-2 : ∀{m n : 人ℕ} -> n ∼ ◌ -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (m ⋆ incl tt)) (incl n) -> ⋆List (Sort 𝒯) × Sort 𝒯
    prop-2 n∼◌ (f ⋆-⧜ incl x) = map (prop-1 n∼◌) f' , (prop-1 n∼◌ x)
      where
        f' = §-⧜𝐒𝐮𝐛𝐬𝐭-⊤.prop-1 {T = SortTerm} (f)

  getCtx : ∀{m n : 人ℕ} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (m ⋆ incl tt)) (incl n) -> ⋆List (SortTermᵈ n)
  -- [ m ]ᶠ -> SortTermᵈ n
  getCtx s = asList (π₀-⋆-⧜ s)

  getRet : ∀{m n : 人ℕ} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (m ⋆ incl tt)) (incl n) -> SortTermᵈ n
  getRet (f ⋆-⧜ incl g) = g

  makeSort : SortTermᵈ ◌ -> Sort 𝒯
  makeSort (con x) = x


  private
    macro
      ℬ : SomeStructure
      ℬ = #structureOn (InductiveSubstitution SortTerm)

    -- l' : UntypedCon 𝒯 -> ℕ
    -- l' (τs , τ , _) = length τs


    -- Edge : ∀{n : 人ℕ} -> (r : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> 𝒰 _
    -- Edge r = ∑ λ s -> ∑ λ t -> TreePath r s ×-𝒰 TreeStep s t

    Vertex : ∀{n : 人ℕ} -> (r : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') -> 𝒰 _
    Vertex r = ∑ TreePath r


    F : 人ℕ -> Functor ℬ (𝐔𝐧𝐢𝐯 ℓ₀)
    F n = f since {!!}
      where
        f : ℬ -> 𝐔𝐧𝐢𝐯 ℓ₀
        f b = (incl (n ⋆ incl tt) ⟶ b)

    module _ {n : 人ℕ} (t : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l') where

      private
        V = Maybe (Vertex t)


      subnode : Vertex t -> SubNode n
      subnode ((node a x , p)) = isNode a
      subnode ((var x , p)) = isVar x

      node' : V -> Node n
      node' (left _) = isTop
      node' (right x) = notTop (subnode x)

      neightop : ∀{s} -> (TreePath t s) -> V
      neightop [] = nothing
      neightop (step p x) = just (_ , p)

      neigh' : (v : V) -> [ size (node' v) ]ᶠ -> V
      -- the top node
      neigh' (left x) i = just (t , [])

      -- -- notTop node, edge down
      -- neigh' (just (var a , _)) (_ , right-∍ ())
      -- neigh' (just (node a x , _)) (_ , right-∍ i) = {!!}

      -- notTop node, edge to the parent
      neigh' (just (t , p)) (_ , left-∍ i) = neightop p
      -- neigh' (just (t , [])) (_ , left-∍ i) = nothing
      -- neigh' (just (t₂ , step {.t} {t₁} {.t₂} p x)) (_ , left-∍ i) = just (t₁ , p)

      -- notTop node, edge down
      neigh' (just (node a ts , p)) (xi , right-∍ i) = just (ts (xi , i) , step p (incl ts (_ , i)))
      -- neigh' (just (node a ts , [])) (xi , right-∍ i) = just (ts (xi , i) , step [] (incl ts (_ , i)))
      -- neigh' (just (node a ts , step s1 s2)) (xi , right-∍ i) = just (ts (xi , i) , step (step s1 s2) (incl _ _))



      isNGraph:Vertex : isNGraph (Node n) size V
      isNGraph.node isNGraph:Vertex = node'
      isNGraph.neigh isNGraph:Vertex = neigh'

      𝒢 : NGraph (Node n) size
      𝒢 = _ since isNGraph:Vertex

      data ContextHasVar {k : 人ℕ} {b : ℬ} (σ : ⟨ F k ⟩ b) (i : [ k ]ᶠ) : 𝒰 ℓ₀ where
        contextHasVar : atList (π₀-⋆-⧜ ⟨ σ ⟩) i ≣ getRet ⟨ σ ⟩ -> ContextHasVar σ i

      -- data CtrTyped {k : 人ℕ} {b : ℬ} (σ : ⟨ F k ⟩ b) (c : UntypedCon 𝒯) : 𝒰 ℓ₀ where

      data isOfType' (b : ℬ) : (nd : Node n) -> ([ size nd ]ᶠ -> ⟨ F n ⟩ b) -> 𝒰 ℓ₀ where
        varType : (i : [ n ]ᶠ) -> (f : [ size (notTop (isVar i)) ]ᶠ -> ⟨ F n ⟩ b)
                  -> ContextHasVar (f (tt , (left-∍ incl))) i
                  -> isOfType' b (notTop (isVar i)) f

        nodeType : ∀{τs : List (Sort 𝒯)} -> {τ : Sort 𝒯} -> {x : Con 𝒯 τs τ}

                   -- the annotations on my edges
                   -> (f : [ size {n = n} (notTop (isNode (_ , _ , x))) ]ᶠ -> ⟨ F n ⟩ b)

                   -- all contexts are the same
                   -> (∀ i j -> getCtx ⟨ f i ⟩ ≡ getCtx ⟨ f j ⟩)

                   -- the output type is the sort of my ctr
                   -> (getRet ⟨ f (tt , left-∍ incl) ⟩ ≡ con τ)

                   -- the input types are given by the ctr inputs
                   -> (∀ ρ -> ∀(i : ι τs ∍ ρ) -> getRet ⟨ f (tt , right-∍ (map-∍ (const tt) i)) ⟩ ≡ con ρ)

                  -> isOfType' b (notTop (isNode (_ , _ , x))) f

        topType : (f : [ incl tt ]ᶠ -> ⟨ F n ⟩ b) -> isOfType' b (isTop) f

      TA : TypingAnnotation (Node n) size (F n) _
      TA = record { isOfType = isOfType' }

      module _ {{_ : isConstantANG (Node n) size (F n) (incl ◌) 𝒢}}
               {{_ : isContracted (Node n) size (F n)}}
               -- {{WT : isWellTyped (Node n) size (F n) TA}}
               (WT : ∀(v : V) -> isOfType' (incl ◌) _ (ann v))
               where

        dKind : (Vertex t) -> 𝒰 _
        dKind v = Term₁-𝕋× 𝒯 (map-⋆List makeSort (asList (π₀-⋆-⧜ σ))) (makeSort (getRet σ))
          where
            σ : Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (n ⋆-⧜ incl tt)) (incl ◌-⧜)
            σ = ⟨ ann (just v) (_ , left-∍ incl) ⟩

        dTermType : Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (n ⋆-⧜ incl tt)) (incl ◌-⧜) -> 𝒰 _
        dTermType σ = Term₁-𝕋× 𝒯 (map-⋆List makeSort (getCtx σ)) (makeSort (getRet σ))



        --- single
        {-# TERMINATING #-}
        dType : (v : Vertex t) -> isOfType' (incl ◌) (node' (just v)) (ann (just v)) -> dKind v

        dType (node (τs , τ , c) ts , p) (nodeType f ctxP outputP inputP) =
          let c₁ : Con 𝒯 τs (makeSort $ getRet ⟨ f (tt , left-∍ incl) ⟩)
              c₁ = transport (λ i -> Con 𝒯 τs (makeSort (outputP (~ i)))) c

              -- build the terms for my subtrees
              ts₁ : ∀(i : [ l' (τs , τ , c) ]ᶠ) -> dTermType ⟨ ann (just (ts i , step p (incl _ _))) (_ , left-∍ incl) ⟩
              ts₁ i = dType (ts i , _) (WT _)

              -- transport over the equality of their outer boundaries to my inner boundaries
              ts₂ : ∀(i : [ l' (τs , τ , c) ]ᶠ) -> dTermType ⟨ ann (just (VecTree.node (τs , τ , c) ts , p)) (_ , right-∍ (i .snd)) ⟩
              ts₂ i = transport (λ k -> dTermType ⟨ iscontr {v = (just (ts i , step p (incl _ _)))}
                                                            {w = (just (VecTree.node (τs , τ , c) ts , p))}
                                                            (_ , left-∍ incl)
                                                            (_ , right-∍ (i .snd))
                                                            refl-≡
                                                            refl-≡
                                                            k ⟩)
                                (ts₁ i)

              -- transport from my inner boundary to the requirements of the con ctr
              ts₃ : ∀{ρ} -> (ι τs ∍ ρ) -> Term₁-𝕋× 𝒯 (map-⋆List makeSort (getCtx ⟨ ann (just (VecTree.node (τs , τ , c) ts , p)) (_ , left-∍ incl) ⟩)) (ρ)
              ts₃ {ρ} i = transport (λ k -> Term₁-𝕋× 𝒯 (map-⋆List makeSort (ctxP (_ , right-∍ (map-∍ _ i)) (_ , left-∍ incl) k))
                                                       (makeSort (inputP ρ i k)))
                                    (ts₂ (_ , map-∍ _ i))

          in con c₁ (fromIndexed ts₃)

        dType (var x , p) (varType i f (contextHasVar q)) = var (map-∍ makeSort (atasList' (π₀-⋆-⧜ σ) i q))
          where
            σ : Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (n ⋆-⧜ incl tt)) (incl ◌-⧜)
            σ = ⟨ ann (just (var x , p)) (_ , left-∍ incl) ⟩

        -- dType : (s : VecTree (UntypedCon 𝒯) ([ n ]ᶠ) l')
        --       -> TreePath t s
        --       -> 

{-
-}
