

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

module _ {๐ : Category ๐} {๐ : Category ๐} where
  Functor:โ : (x : โจ ๐ โฉ) -> Functor ๐ ๐
  โจ Functor:โ x โฉ = โ x
  IFunctor.map (of Functor:โ x) _ = id
  IFunctor.functoriality-id (of Functor:โ x) = refl
  IFunctor.functoriality-โ (of Functor:โ x) = unit-2-โ โปยน
  IFunctor.functoriality-โฃ (of Functor:โ x) _ = refl

--------------------------------------------------------------------
-- == Recursion Monads
-- (T : Functor ` IdxSet K ๐ ` ` IdxSet K ๐ `)

module _ {๐ : Category ๐} where
  ฮผ : (T : Monad ๐) -> (โจ T โฉ โ โจ T โฉ โถ โจ T โฉ)
  ฮผ T = โฒ join {{of T}} โฒ

module _ {K : ๐ฐ ๐} (D : IQuiver K (๐ , ๐)) where
  Decomp : Functor ` IdxSet K ๐ ` ` IdxSet K ๐ `
  โจ โจ Decomp โฉ X โฉ k = โ{kโ : K} -> (e : Edge {{D}} kโ k) -> Maybe (โจ X โฉ kโ)
  of โจ Decomp โฉ X = {!!}
  โจ IFunctor.map (of Decomp) f โฉ x e = map-Maybe (โจ f โฉ) (x e)
  of IFunctor.map (of Decomp) x = record {}
  IFunctor.functoriality-id (of Decomp) = {!!}
  IFunctor.functoriality-โ (of Decomp) = {!!}
  IFunctor.functoriality-โฃ (of Decomp) = {!!}


-- [Definition]
-- | A \textbf{recursion monad} is given by a monad \AB{T}, together with a pointed set \AFd{Direction}
-- and an action of this on any set $\AB{T} A$.
module _ {K : ๐ฐ ๐} where
  record IRecAccessible (T : Monad ` IdxSet K ๐ `) : ๐ฐ (๐ ๏ฝค ๐ โบ) where

    -- field depth : โ{A k} -> โจ โจ T โฉ A โฉ k -> โ
    --       depth/return : โ{A : K -> ๐ฐ ๐} -> {{_ : IIdxSet K A}} -> โ{k : K} -> โ{a : A k} -> depth (โจ return {A = ` A `} โฉ k a) โก 0
    field Dir : IQuiver K (๐ , ๐)
          {{ISet:Dir}} : โ{a b : K} -> ISet (Edge {{Dir}} a b)
          {{ISet:K}} : ISet K
          {{IDiscreteStr:Dir}} : โ{a b : K} -> IDiscreteStr (Edge {{Dir}} a b)
          {{IDiscreteStr:K}} : IDiscreteStr K

    field decompose : Natural โจ T โฉ (โจ T โฉ โ Decomp Dir)
          -- commutes:decompose : commutes-Nat (ฮผ T) decompose
          -- {{IMono:decompose}} : IMono decompose
          -- wellfounded : WellFounded (ฮป (a b : K) -> QPath a b)
          -- pts : Natural (Functor:โ ๐) โจ T โฉ

    ฮด : โ{A} -> โ{k} -> โ(a : โจ โจ โจ T โฉ โฉ A โฉ k) -> โ{j} -> (e : Edge {{Dir}} j k) -> Maybe (โจ โจ โจ T โฉ โฉ A โฉ j)
    ฮด a e = โจ โจ decompose โฉ โฉ a e

    field ฮด-comm : โ{X Y} -> โ(f : X โถ โจ โจ T โฉ โฉ Y) -> โ{j k} -> โ(e : Edge {{Dir}} k j) (x : โจ โจ โจ T โฉ โฉ X โฉ j) -> (ฮด x e โข nothing) -> map-Maybe (โจ map f โ join {{of T}} โฉ {_}) (ฮด x e) โก ฮด (โจ map f โ join {{of T}} โฉ x) e

    field e0 : โ{k} {X : IdxSet K ๐} -> โจ โจ โจ T โฉ โฉ X โฉ k
          -- e0-adsorb : โ{k j : K} {X : IdxSet K ๐} -> (e : Edge {{Dir}} j k) -> ฮด (e0 {X = X}) e โก just e0
          -- cancel-e0 : โ{k : K} {X : IdxSet K ๐} -> (x : โจ โจ โจ T โฉ โฉ X โฉ k) -> (โ{j} -> (e : Edge {{Dir}} j k) -> ฮด x e โก just x) -> x โก e0
    -- e0 {k} = โจ โจ pts โฉ โฉ (โฅ tt)


    field a0 : โ{k : K} -> Edge {{Dir}} k k
          a0-adsorb : โ{k : K} -> โ{X} -> โ(x : โจ โจ โจ T โฉ โฉ X โฉ k ) -> ฮด x (a0 {k}) โก just e0
          -- cancel-e0 : โ{k : K} -> โ{X} -> โ(x : โจ โจ โจ T โฉ โฉ X โฉ k ) -> (ฮด x (a0 {k}) โก just x) -> x โก e0

    field k-a1 : K -> K
          a1 : โ{k} -> Edge {{Dir}} (k-a1 k) k

    isDecomposable : โ{k} {X} -> โจ โจ โจ T โฉ โฉ X โฉ k -> ๐ฐ _
    isDecomposable {k} x = โ {j} -> โ (e : Edge {{Dir}} j k) -> โ ฮป y -> ฮด x e โก-Str just y

    isPure : โ{k} {X} -> โจ โจ โจ T โฉ โฉ X โฉ k -> ๐ฐ _
    isPure {k} {X} x = (ฮด x a1 โก-Str nothing) ร-๐ฐ ((โ ฮป (x' : โจ X โฉ k) -> (x โก-Str โจ return {{of T}} โฉ x')))

    field isDecomposableP : โ{k} {X} -> โจ โจ โจ T โฉ โฉ X โฉ k -> ๐ฐ ๐
          isPureP   : โ{k} {X} -> โจ โจ โจ T โฉ โฉ X โฉ k -> ๐ฐ ๐
          decideDecompose : โ{k X} -> (x : โจ โจ โจ T โฉ โฉ X โฉ k) -> (isPureP x +-๐ฐ isDecomposableP x)
          decide-e0 : โ{k X} -> (x : โจ โจ โจ T โฉ โฉ X โฉ k) -> Decision (x โก-Str e0)
          makeDec : โ{k X} -> {x : โจ โจ โจ T โฉ โฉ X โฉ k} -> isDecomposableP x -> isDecomposable x
          makePure : โ{k X} -> {x : โจ โจ โจ T โฉ โฉ X โฉ k} -> isPureP x -> isPure x

    _โบ_ : โ{X} -> (โ โจ โจ โจ T โฉ โฉ X โฉ) -> (โ โจ โจ โจ T โฉ โฉ X โฉ) -> ๐ฐ _
    _โบ_ = ฮป {(k , x) (j , y) -> (y โข-Str e0) ร-๐ฐ (โ ฮป (e : Edge {{Dir}} k j) -> ฮด y e โก-Str just x)}

    -- field decideDecompose : โ{k} {X} -> (x : โจ โจ โจ T โฉ โฉ X โฉ k) -> isPure x +-๐ฐ isDecomposable x
    field _โบP_ : โ{X} -> (โ โจ โจ โจ T โฉ โฉ X โฉ) -> (โ โจ โจ โจ T โฉ โฉ X โฉ) -> ๐ฐ ๐
          recreate-โบ : โ{X} -> {x y : โ โจ โจ โจ T โฉ โฉ X โฉ} -> (x โบ y) -> x โบP y
    field isWellfounded::โบP : โ{X} -> WellFounded (_โบP_ {X})
    field cancel-ฮด : โ{k} {X} -> (x y : โจ โจ โจ T โฉ โฉ X โฉ k) -> isDecomposableP x -> isDecomposableP y -> (โ{j} -> โ(e : Edge {{Dir}} j k) -> ฮด x e โก ฮด y e) -> x โก y


    -- isVariable : โ{k} {X} -> โจ โจ โจ T โฉ โฉ X โฉ k -> ๐ฐ _
    -- isVariable {k} x = โ j -> โ (e : Edge {{Dir}} j k) -> (e โข a0) -> ฮด x e โก nothing



    -- field ฮด-cancel : 

    --       strict : โ{A} -> โ(x : โจ T โฉ A) -> on-Decom T Dir (ฮป a -> x โก return a) (ฮป a -> depth a < depth x) (โจ decompose โฉ x)

  open IRecAccessible {{...}} public


-- //

{-


module _ (T : Functor ` ๐ฐ ๐ ` ` ๐ฐ ๐ `) (D : ๐ฐ ๐) where
  Decom : Functor ` ๐ฐ ๐ ` ` ๐ฐ ๐ `
  โจ Decom โฉ X = X +-๐ฐ (D -> โจ T โฉ X)
  IFunctor.map (of Decom) f (left x) = left (f x)
  IFunctor.map (of Decom) f (just x) = right (ฮป d -> map f (x d))
  IFunctor.functoriality-id (of Decom) = {!!}
  IFunctor.functoriality-โ (of Decom) = {!!}
  IFunctor.functoriality-โฃ (of Decom) = {!!}

  -- data on-Decom {A : ๐ฐ ๐} (P : โจ T โฉ A -> ๐ฐ ๐) : โจ Decom โฉ A -> ๐ฐ (๐ ๏ฝค ๐) where
  --   isLeft : โ{a : A} -> on-Decom P ()

  on-Decom : โ {A} -> (A -> ๐ฐ (๐ ๏ฝค ๐)) -> (โจ T โฉ A -> ๐ฐ ๐) -> โจ Decom โฉ A -> ๐ฐ (๐ ๏ฝค ๐)
  on-Decom P Q (left x) = P x
  on-Decom P Q (just x) = โ d -> Q (x d)

module _ (T : Functor ` ๐ฐ ๐ ` ` ๐ฐ ๐ `) {{_ : IMonad T}} where
  -- "recursively accessible"
  record IRecAccessible-Monad : ๐ฐ (๐ โบ) where

    field depth : โ{A} -> โจ T โฉ A -> โ
          depth/return : โ{A : ๐ฐ ๐} -> โ{a : A} -> depth (return a) โก 0
    field Dir : ๐ฐ ๐

    field decompose : Natural T (Decom T Dir)
          {{IMono:decompose}} : IMono decompose
          strict : โ{A} -> โ(x : โจ T โฉ A) -> on-Decom T Dir (ฮป a -> x โก return a) (ฮป a -> depth a < depth x) (โจ decompose โฉ x)

  open IRecAccessible-Monad {{...}} public

-}


{-
record IRecMonad (T : Functor (โ ๐ฐโ) (โ ๐ฐโ)) : ๐ฐโ where
  field {{SetMonadInstance}} : ISetMonad T
        Direction : ๐ฐโ
        {{PointedInstance}} : IPointed Direction
        depth : โ{A} -> โจ T โฉ A -> โ
        depth/bind : โ{A B} -> (a : โจ T โฉ A) -> (f : A -> โจ T โฉ B) -> {n : โ} -> depth a โก suc n -> โ ฮป m -> depth (a >>= f) โก suc m
        go-zero : โ{A} -> (a : โจ T โฉ A) -> depth a โก 0 -> A
        go-zero/id : โ{A} -> (a : โจ T โฉ A) -> (p : depth a โก 0) -> return (go-zero a p) โก a
        go-suc : โ{A} -> (a : โจ T โฉ A) -> {n : โ} -> depth a โก suc n -> Direction -> โจ T โฉ A
        go-suc/depth : โ{A} -> (a : โจ T โฉ A) -> {n : โ} -> (p : depth a โก suc n) -> (d : Direction) -> depth (go-suc a p d) โค n
        go-suc/bind : โ{A B} -> (a : โจ T โฉ A) -> (f : A -> โจ T โฉ B) -> {n : โ} -> (p : depth a โก suc n) -> (d : Direction) -> go-suc a p d >>= f โก go-suc (a >>= f) (depth/bind a f p .snd) d
        cancel-go-suc : โ{A} -> (a b : โจ T โฉ A) {n m : โ} -> (p : depth a โก suc n) -> (q : depth b โก suc m)
                        -> (โ d -> go-suc a p d โก go-suc b q d) -> a โก b
-}
{-
        --- go : โ {A} -> Direction -> (T A) -> A +-๐ฐ (T A)
        --- go/>>= : โ{A B x} -> {a a' : โจ T โฉ A} -> (f : A -> โจ T โฉ B) -> go x a โก right a' -> go x (a >>= f) โก right (a' >>= f)
        --- depth/go-right : โ{A} -> (a a' : โจ T โฉ A) -> โ d -> go d a โก right a' -> depth a' <-โ depth a
        --- depth-ret : โ{A} -> {a : โจ T โฉ A} -> depth a โก 0 -> โ ฮป (a' : A) -> a โก return a'
        --- cancel-go : โ{A} -> (a b : โจ T โฉ A) -> (โ d -> go d a โก go d b) -> a โก b

open IRecMonad {{...}} public

unquoteDecl RecMonad derivationMonad = #struct (quote IRecMonad) "T" RecMonad derivationMonad
-- //

-- [Example]
-- | We show that \AD{Type}, as defined in the last section is a recursion monad.
-- | The set of directions is given by:
data Direction-Type : ๐ฐโ where
  dir-โ1      : Direction-Type
  dir-โ2      : Direction-Type
  dir-MyBool  : Direction-Type
  dir-MyNat   : Direction-Type

-- | The depth is simply given by the depth of the AST.
depth-Type : โ {A} -> Type A -> โ
depth-Type (t โ s) = suc (max-โ (depth-Type t) (depth-Type s))
depth-Type MyBool = 1
depth-Type MyNat = 1
depth-Type (var x) = 0

-- | The instance is as follows:
IRecMonad:Type : IRecMonad (โ Type)
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



