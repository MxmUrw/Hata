

module Verification.Unification.RecAccessible where

open import Verification.Conventions
open import Verification.Core.Type
-- open import Verification.Core.Algebra
open import Verification.Core.Order
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Monad
open import Verification.Core.Category.EpiMono
open import Verification.Core.Category.Natural
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.TypeProperties
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Kan.Terminal
open import Verification.Core.Homotopy.Level
open import Verification.Core.Order.Instance.Level
--- open import Verification.Core.Category.Limit
-- open import Verification.Unification.Substitution

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  Functor:∆ : (x : ⟨ 𝒟 ⟩) -> Functor 𝒞 𝒟
  ⟨ Functor:∆ x ⟩ = ∆ x
  IFunctor.map (of Functor:∆ x) _ = id
  IFunctor.functoriality-id (of Functor:∆ x) = refl
  IFunctor.functoriality-◆ (of Functor:∆ x) = unit-2-◆ ⁻¹
  IFunctor.functoriality-≣ (of Functor:∆ x) _ = refl

--------------------------------------------------------------------
-- == Recursion Monads
-- (T : Functor ` IdxSet K 𝑖 ` ` IdxSet K 𝑖 `)

module _ {𝒞 : Category 𝑖} where
  μ : (T : Monad 𝒞) -> (⟨ T ⟩ ◆ ⟨ T ⟩ ⟶ ⟨ T ⟩)
  μ T = ′ join {{of T}} ′

module _ {K : 𝒰 𝑖} (D : IQuiver K (𝑖 , 𝑖)) where
  Decomp : Functor ` IdxSet K 𝑖 ` ` IdxSet K 𝑖 `
  ⟨ ⟨ Decomp ⟩ X ⟩ k = ∀{k₂ : K} -> (e : Edge {{D}} k₂ k) -> Maybe (⟨ X ⟩ k₂)
  of ⟨ Decomp ⟩ X = {!!}
  ⟨ IFunctor.map (of Decomp) f ⟩ x e = map-Maybe (⟨ f ⟩) (x e)
  of IFunctor.map (of Decomp) x = record {}
  IFunctor.functoriality-id (of Decomp) = {!!}
  IFunctor.functoriality-◆ (of Decomp) = {!!}
  IFunctor.functoriality-≣ (of Decomp) = {!!}


-- [Definition]
-- | A \textbf{recursion monad} is given by a monad \AB{T}, together with a pointed set \AFd{Direction}
-- and an action of this on any set $\AB{T} A$.
module _ {K : 𝒰 𝑖} where
  record IRecAccessible (T : Monad ` IdxSet K 𝑖 `) : 𝒰 (𝑖 ､ 𝑖 ⁺) where

    -- field depth : ∀{A k} -> ⟨ ⟨ T ⟩ A ⟩ k -> ℕ
    --       depth/return : ∀{A : K -> 𝒰 𝑖} -> {{_ : IIdxSet K A}} -> ∀{k : K} -> ∀{a : A k} -> depth (⟨ return {A = ` A `} ⟩ k a) ≡ 0
    field Dir : IQuiver K (𝑖 , 𝑖)
          {{ISet:Dir}} : ∀{a b : K} -> ISet (Edge {{Dir}} a b)
          {{ISet:K}} : ISet K
          {{IDiscreteStr:Dir}} : ∀{a b : K} -> IDiscreteStr (Edge {{Dir}} a b)
          {{IDiscreteStr:K}} : IDiscreteStr K

    field decompose : Natural ⟨ T ⟩ (⟨ T ⟩ ◆ Decomp Dir)
          -- commutes:decompose : commutes-Nat (μ T) decompose
          -- {{IMono:decompose}} : IMono decompose
          -- wellfounded : WellFounded (λ (a b : K) -> QPath a b)
          -- pts : Natural (Functor:∆ 𝟙) ⟨ T ⟩

    δ : ∀{A} -> ∀{k} -> ∀(a : ⟨ ⟨ ⟨ T ⟩ ⟩ A ⟩ k) -> ∀{j} -> (e : Edge {{Dir}} j k) -> Maybe (⟨ ⟨ ⟨ T ⟩ ⟩ A ⟩ j)
    δ a e = ⟨ ⟨ decompose ⟩ ⟩ a e

    field δ-comm : ∀{X Y} -> ∀(f : X ⟶ ⟨ ⟨ T ⟩ ⟩ Y) -> ∀{j k} -> ∀(e : Edge {{Dir}} k j) (x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ j) -> (δ x e ≢ nothing) -> map-Maybe (⟨ map f ◆ join {{of T}} ⟩ {_}) (δ x e) ≡ δ (⟨ map f ◆ join {{of T}} ⟩ x) e

    field e0 : ∀{k} {X : IdxSet K 𝑖} -> ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k
          -- e0-adsorb : ∀{k j : K} {X : IdxSet K 𝑖} -> (e : Edge {{Dir}} j k) -> δ (e0 {X = X}) e ≡ just e0
          -- cancel-e0 : ∀{k : K} {X : IdxSet K 𝑖} -> (x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k) -> (∀{j} -> (e : Edge {{Dir}} j k) -> δ x e ≡ just x) -> x ≡ e0
    -- e0 {k} = ⟨ ⟨ pts ⟩ ⟩ (↥ tt)


    field a0 : ∀{k : K} -> Edge {{Dir}} k k
          a0-adsorb : ∀{k : K} -> ∀{X} -> ∀(x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k ) -> δ x (a0 {k}) ≡ just e0
          -- cancel-e0 : ∀{k : K} -> ∀{X} -> ∀(x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k ) -> (δ x (a0 {k}) ≡ just x) -> x ≡ e0

    field k-a1 : K -> K
          a1 : ∀{k} -> Edge {{Dir}} (k-a1 k) k

    isDecomposable : ∀{k} {X} -> ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k -> 𝒰 _
    isDecomposable {k} x = ∀ {j} -> ∀ (e : Edge {{Dir}} j k) -> ∑ λ y -> δ x e ≡-Str just y

    isPure : ∀{k} {X} -> ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k -> 𝒰 _
    isPure {k} {X} x = (δ x a1 ≡-Str nothing) ×-𝒰 ((∑ λ (x' : ⟨ X ⟩ k) -> (x ≡-Str ⟨ return {{of T}} ⟩ x')))

    field isDecomposableP : ∀{k} {X} -> ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k -> 𝒰 𝑖
          isPureP   : ∀{k} {X} -> ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k -> 𝒰 𝑖
          decideDecompose : ∀{k X} -> (x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k) -> (isPureP x +-𝒰 isDecomposableP x)
          decide-e0 : ∀{k X} -> (x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k) -> Decision (x ≡-Str e0)
          makeDec : ∀{k X} -> {x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k} -> isDecomposableP x -> isDecomposable x
          makePure : ∀{k X} -> {x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k} -> isPureP x -> isPure x

    _≺_ : ∀{X} -> (∑ ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩) -> (∑ ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩) -> 𝒰 _
    _≺_ = λ {(k , x) (j , y) -> (y ≢-Str e0) ×-𝒰 (∑ λ (e : Edge {{Dir}} k j) -> δ y e ≡-Str just x)}

    -- field decideDecompose : ∀{k} {X} -> (x : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k) -> isPure x +-𝒰 isDecomposable x
    field _≺P_ : ∀{X} -> (∑ ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩) -> (∑ ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩) -> 𝒰 𝑖
          recreate-≺ : ∀{X} -> {x y : ∑ ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩} -> (x ≺ y) -> x ≺P y
    field isWellfounded::≺P : ∀{X} -> WellFounded (_≺P_ {X})
    field cancel-δ : ∀{k} {X} -> (x y : ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k) -> isDecomposableP x -> isDecomposableP y -> (∀{j} -> ∀(e : Edge {{Dir}} j k) -> δ x e ≡ δ y e) -> x ≡ y


    -- isVariable : ∀{k} {X} -> ⟨ ⟨ ⟨ T ⟩ ⟩ X ⟩ k -> 𝒰 _
    -- isVariable {k} x = ∀ j -> ∀ (e : Edge {{Dir}} j k) -> (e ≢ a0) -> δ x e ≡ nothing



    -- field δ-cancel : 

    --       strict : ∀{A} -> ∀(x : ⟨ T ⟩ A) -> on-Decom T Dir (λ a -> x ≡ return a) (λ a -> depth a < depth x) (⟨ decompose ⟩ x)

  open IRecAccessible {{...}} public


-- //

{-


module _ (T : Functor ` 𝒰 𝑖 ` ` 𝒰 𝑖 `) (D : 𝒰 𝑖) where
  Decom : Functor ` 𝒰 𝑖 ` ` 𝒰 𝑖 `
  ⟨ Decom ⟩ X = X +-𝒰 (D -> ⟨ T ⟩ X)
  IFunctor.map (of Decom) f (left x) = left (f x)
  IFunctor.map (of Decom) f (just x) = right (λ d -> map f (x d))
  IFunctor.functoriality-id (of Decom) = {!!}
  IFunctor.functoriality-◆ (of Decom) = {!!}
  IFunctor.functoriality-≣ (of Decom) = {!!}

  -- data on-Decom {A : 𝒰 𝑖} (P : ⟨ T ⟩ A -> 𝒰 𝑗) : ⟨ Decom ⟩ A -> 𝒰 (𝑖 ､ 𝑗) where
  --   isLeft : ∀{a : A} -> on-Decom P ()

  on-Decom : ∀ {A} -> (A -> 𝒰 (𝑖 ､ 𝑗)) -> (⟨ T ⟩ A -> 𝒰 𝑗) -> ⟨ Decom ⟩ A -> 𝒰 (𝑖 ､ 𝑗)
  on-Decom P Q (left x) = P x
  on-Decom P Q (just x) = ∀ d -> Q (x d)

module _ (T : Functor ` 𝒰 𝑖 ` ` 𝒰 𝑖 `) {{_ : IMonad T}} where
  -- "recursively accessible"
  record IRecAccessible-Monad : 𝒰 (𝑖 ⁺) where

    field depth : ∀{A} -> ⟨ T ⟩ A -> ℕ
          depth/return : ∀{A : 𝒰 𝑖} -> ∀{a : A} -> depth (return a) ≡ 0
    field Dir : 𝒰 𝑖

    field decompose : Natural T (Decom T Dir)
          {{IMono:decompose}} : IMono decompose
          strict : ∀{A} -> ∀(x : ⟨ T ⟩ A) -> on-Decom T Dir (λ a -> x ≡ return a) (λ a -> depth a < depth x) (⟨ decompose ⟩ x)

  open IRecAccessible-Monad {{...}} public

-}


{-
record IRecMonad (T : Functor (⌘ 𝒰₀) (⌘ 𝒰₀)) : 𝒰₁ where
  field {{SetMonadInstance}} : ISetMonad T
        Direction : 𝒰₀
        {{PointedInstance}} : IPointed Direction
        depth : ∀{A} -> ⟨ T ⟩ A -> ℕ
        depth/bind : ∀{A B} -> (a : ⟨ T ⟩ A) -> (f : A -> ⟨ T ⟩ B) -> {n : ℕ} -> depth a ≡ suc n -> ∑ λ m -> depth (a >>= f) ≡ suc m
        go-zero : ∀{A} -> (a : ⟨ T ⟩ A) -> depth a ≡ 0 -> A
        go-zero/id : ∀{A} -> (a : ⟨ T ⟩ A) -> (p : depth a ≡ 0) -> return (go-zero a p) ≡ a
        go-suc : ∀{A} -> (a : ⟨ T ⟩ A) -> {n : ℕ} -> depth a ≡ suc n -> Direction -> ⟨ T ⟩ A
        go-suc/depth : ∀{A} -> (a : ⟨ T ⟩ A) -> {n : ℕ} -> (p : depth a ≡ suc n) -> (d : Direction) -> depth (go-suc a p d) ≤ n
        go-suc/bind : ∀{A B} -> (a : ⟨ T ⟩ A) -> (f : A -> ⟨ T ⟩ B) -> {n : ℕ} -> (p : depth a ≡ suc n) -> (d : Direction) -> go-suc a p d >>= f ≡ go-suc (a >>= f) (depth/bind a f p .snd) d
        cancel-go-suc : ∀{A} -> (a b : ⟨ T ⟩ A) {n m : ℕ} -> (p : depth a ≡ suc n) -> (q : depth b ≡ suc m)
                        -> (∀ d -> go-suc a p d ≡ go-suc b q d) -> a ≡ b
-}
{-
        --- go : ∀ {A} -> Direction -> (T A) -> A +-𝒰 (T A)
        --- go/>>= : ∀{A B x} -> {a a' : ⟨ T ⟩ A} -> (f : A -> ⟨ T ⟩ B) -> go x a ≡ right a' -> go x (a >>= f) ≡ right (a' >>= f)
        --- depth/go-right : ∀{A} -> (a a' : ⟨ T ⟩ A) -> ∀ d -> go d a ≡ right a' -> depth a' <-ℕ depth a
        --- depth-ret : ∀{A} -> {a : ⟨ T ⟩ A} -> depth a ≡ 0 -> ∑ λ (a' : A) -> a ≡ return a'
        --- cancel-go : ∀{A} -> (a b : ⟨ T ⟩ A) -> (∀ d -> go d a ≡ go d b) -> a ≡ b

open IRecMonad {{...}} public

unquoteDecl RecMonad derivationMonad = #struct (quote IRecMonad) "T" RecMonad derivationMonad
-- //

-- [Example]
-- | We show that \AD{Type}, as defined in the last section is a recursion monad.
-- | The set of directions is given by:
data Direction-Type : 𝒰₀ where
  dir-⇒1      : Direction-Type
  dir-⇒2      : Direction-Type
  dir-MyBool  : Direction-Type
  dir-MyNat   : Direction-Type

-- | The depth is simply given by the depth of the AST.
depth-Type : ∀ {A} -> Type A -> ℕ
depth-Type (t ⇒ s) = suc (max-ℕ (depth-Type t) (depth-Type s))
depth-Type MyBool = 1
depth-Type MyNat = 1
depth-Type (var x) = 0

-- | The instance is as follows:
IRecMonad:Type : IRecMonad (⌘ Type)
IRecMonad.SetMonadInstance IRecMonad:Type = IMonad:Type
IRecMonad.Direction IRecMonad:Type = Direction-Type
IPointed.pt (IRecMonad.PointedInstance IRecMonad:Type) = dir-MyBool
IRecMonad.depth IRecMonad:Type = depth-Type
IRecMonad.depth/bind IRecMonad:Type = {!!}
IRecMonad.go-zero IRecMonad:Type = {!!}
IRecMonad.go-zero/id IRecMonad:Type = {!!}
IRecMonad.go-suc IRecMonad:Type = {!!}
IRecMonad.go-suc/depth IRecMonad:Type = {!!}
IRecMonad.go-suc/bind IRecMonad:Type = {!!}
IRecMonad.cancel-go-suc IRecMonad:Type = {!!}

-- //




-}



