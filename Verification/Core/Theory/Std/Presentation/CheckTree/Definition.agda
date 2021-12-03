
module Verification.Core.Theory.Std.Presentation.CheckTree.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Function.Surjective
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Sum.Instance.Functor
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.Semiring

-- module _ {ℬ : 𝒰 𝑖} {{_ : isCategory {𝑗} ℬ}} where
--   data ArrowTree : ℬ -> 𝒰 (𝑖 ､ 𝑗) where
--     incl : (b : ℬ) -> ArrowTree b
--     _⋆-⧜_ : ∀{a b c : ℬ}
--             -> (ArrowTree b × (b ⟶ a))
--             -> (ArrowTree c × (c ⟶ a))
--             -> ArrowTree a

-- module _ {ℬ : 𝒰 𝑖} {{_ : isCategory {𝑗} ℬ}} where
--   data _∍-AT_ : {b : ℬ} (t : ArrowTree b) (x : ℬ) -> 𝒰 (𝑖 ､ 𝑗) where
--     incl : ∀{b : ℬ} -> incl b ∍-AT b

--     left-∍ : ∀{a b c : ℬ} {x : ℬ}
--             -> (t1 : ArrowTree b) (f1 : b ⟶ a)
--             -> (t2 : ArrowTree c) (f2 : c ⟶ a)
--             -> t1 ∍-AT x
--             -> ((t1 , f1) ⋆-⧜ (t2 , f2)) ∍-AT x

--     right-∍ : ∀{a b c : ℬ} {x : ℬ}
--             -> (t1 : ArrowTree b) (f1 : b ⟶ a)
--             -> (t2 : ArrowTree c) (f2 : c ⟶ a)
--             -> t2 ∍-AT x
--             -> ((t1 , f1) ⋆-⧜ (t2 , f2)) ∍-AT x

module _ {A : 𝒰 𝑖} {{_ : isSet-Str A}} where
  rem₂ : ∀(as : ⋆List A) -> {a1 a2 : A} -> (a1p : as ∍ a1) -> (a2p : as ∍ a2) -> (a1p ≠-∍ a2p) -> ⋆List A
  rem₂ as a1p a2p 1≠2 = (as \\ a2p) \\ (skip-∍ a1p a2p 1≠2)

module _ {ℬ : 𝒰 𝑖} {{_ : isCategory {𝑗} ℬ}} {{_ : isSet-Str ℬ}} where
  data ArrowTree : (⋆List ℬ) -> ℬ -> 𝒰 (𝑖 ､ 𝑗) where
    incl : (b : ℬ) -> ArrowTree (incl b) b
    _∧-⧜_ : ∀{a b c : ℬ} {bs cs}
            -> (ArrowTree bs b × (b ⟶ a))
            -> (ArrowTree cs c × (c ⟶ a))
            -> ArrowTree (bs ⋆ cs) a

  data ArrowForrest : (⋆List ℬ) -> (⋆List ℬ) -> 𝒰 (𝑖 ､ 𝑗) where
    incl : ∀{as b} -> ArrowTree as b -> ArrowForrest as (incl b)
    _⋆-⧜_ : ∀{as bs cs ds}
          -> ArrowForrest as bs
          -> ArrowForrest cs ds
          -> ArrowForrest (as ⋆ cs) (bs ⋆ ds)
    ◌-⧜ : ArrowForrest ◌ ◌


  id-矢森 : ∀{as} -> ArrowForrest as as
  id-矢森 {incl x} = incl (incl x)
  id-矢森 {as ⋆-⧜ bs} = id-矢森 ⋆-⧜ id-矢森
  id-矢森 {◌-⧜} = ◌-⧜

  -- 矢木 as b -> 矢森 as (incl b)
  -- 矢森 as bs -> 矢森 cs ds -> 矢森 (as ⋆ cs) (bs ⋆ ds)

  data Link-AF : {as0 as bs : ⋆List ℬ} -> ∀{a b} -> (t : ArrowTree as0 b) (ts : ArrowForrest as bs) -> (as0 ∍ a) -> (as ∍ a) -> (bs ∍ b) -> 𝒰 (𝑖 ､ 𝑗) where
    incl : ∀{as a b} -> {t : ArrowTree as b} -> (as∍a : as ∍ a) -> Link-AF t (incl t) as∍a as∍a incl
    left-∍ : ∀{as bs cs ds} -> ∀{a b as0}
          -> {t : ArrowTree as0 b}
          -> {ts : ArrowForrest as bs}
          -> {us : ArrowForrest cs ds}
          -> {q : as0 ∍ a}
          -> {p0 : as ∍ a} -> {p1 : bs ∍ b}
          -> Link-AF t ts q p0 p1
          -> Link-AF t (ts ⋆-⧜ us) q (left-∍ p0) (left-∍ p1)
    right-∍ : ∀{as bs cs ds} -> ∀{a b as0}
          -> {t : ArrowTree as0 b}
          -> {ts : ArrowForrest as bs}
          -> {us : ArrowForrest cs ds}
          -> {q : as0 ∍ a}
          -> {p0 : cs ∍ a} -> {p1 : ds ∍ b}
          -> Link-AF t us q p0 p1
          -> Link-AF t (ts ⋆-⧜ us) q (right-∍ p0) (right-∍ p1)

  record MiniLink-AF {as bs : ⋆List ℬ} {a b} (ts : ArrowForrest as bs) (p0 : as ∍ a) (p1 : bs ∍ b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor minilink
    field {sublist-Link} : ⋆List ℬ
    field sublist-member : sublist-Link ∍ a
    field subtree-Link   : ArrowTree sublist-Link b
    field minilink-Link  : Link-AF subtree-Link ts sublist-member p0 p1

  open MiniLink-AF public

  record MicroLink-AF {as bs : ⋆List ℬ} {b} (ts : ArrowForrest as bs) (p1 : bs ∍ b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor microlink
    field {member0el} : ℬ
    field {member0} : as ∍ member0el
    field microlink-Link : MiniLink-AF ts member0 p1

  open MicroLink-AF public


  _\\-AF_ : ∀{as bs as0 : ⋆List ℬ} -> ∀{a b}
        -> (ts : ArrowForrest as bs)
        -> {t : ArrowTree as0 b}
        -> {q : as0 ∍ a} -> {p0 : as ∍ a} -> {p1 : bs ∍ b}
        -> Link-AF t ts q p0 p1
        -> ∑ λ rs -> ArrowForrest rs (bs \\ p1) × (𝑒𝑙 rs ⋆ 𝑒𝑙 as0 ∼ 𝑒𝑙 as)
  (incl _) \\-AF incl t = _ , ◌-⧜ , pres-⋆ ⁻¹ ∙ (cong-∼ unit-l-⋆)
  (ts ⋆-⧜ us) \\-AF left-∍ l =
    let (rs' , ts' , rsp) = ts \\-AF l
    in _ , ((ts' ⋆-⧜ us) , {!!})
  (ts ⋆-⧜ us) \\-AF right-∍ l =
    let (rs' , us' , rsp) = us \\-AF l
    in _ , ((ts ⋆-⧜ us') , {!!})

  -- getLink-Tree : ∀{as b} -> ∀{a} (t : ArrowTree as b) (p0 : as ∍ a) -> ∑ λ (p1 : incl b ∍ a) -> MiniLink-AF (incl t) p0 p1
  -- getLink-Tree (incl _) (incl) = incl , (minilink _ (incl _) (incl incl))
  -- getLink-Tree (x ∧-⧜ y) (right-∍ p0) = {!!}
  -- getLink-Tree ((x , fx) ∧-⧜ (y , fy)) (left-∍ p0) with getLink-Tree x p0
  -- ... | incl , minilink q t link = {!!} , {!!}

  getLink : {as bs : ⋆List ℬ} -> ∀{a} (ts : ArrowForrest as bs) (p0 : as ∍ a) -> ∑ λ b -> ∑ λ (p1 : bs ∍ b) -> MiniLink-AF ts p0 p1
  getLink (incl x) p0 = _ , incl , (minilink p0 x (incl p0))
  getLink (ts ⋆-⧜ us) (right-∍ p0) =
    let b , p1 , (minilink pt t link) = getLink us p0
    in b , ((right-∍ p1) , (minilink pt t (right-∍ link )))
  getLink (ts ⋆-⧜ us) (left-∍ p0) =
    let b , p1 , (minilink pt t link) = getLink ts p0
    in b , ((left-∍ p1) , (minilink pt t (left-∍ link )))

  treehom : {as0 : ⋆List ℬ} -> ∀{a b} -> (t : ArrowTree as0 b) -> (p : as0 ∍ a) -> a ⟶ b
  treehom (incl _) incl = id
  treehom (x ∧-⧜ (y , fy)) (right-∍ p) = treehom y p ◆ fy
  treehom ((x , fx) ∧-⧜ y) (left-∍ p) = treehom x p ◆ fx

  linkhom : {as bs : ⋆List ℬ} -> ∀{a b} -> {ts : ArrowForrest as bs} {p0 : as ∍ a} -> {p1 : bs ∍ b} -> (l : MiniLink-AF ts p0 p1) -> a ⟶ b
  linkhom (minilink sublist-member subtree-Link minilink-Link) = f minilink-Link
    where
      f : {as0 as bs : ⋆List ℬ} -> ∀{a b} -> {t : ArrowTree as0 b} {ts : ArrowForrest as bs} -> {q : as0 ∍ a} -> {p0 : as ∍ a} -> {p1 : bs ∍ b}
          -> Link-AF t ts q p0 p1 -> a ⟶ b
      f {t = t} (incl p) = treehom t p
      f (left-∍ l) = f l
      f (right-∍ l) = f l

  merge-AF : ∀{as bs : ⋆List ℬ}
        -> (ts : ArrowForrest as bs)
        -> {b1 b1' b2 b2' x : ℬ}
        -> {b1p : as ∍ b1} -> {b2p : as ∍ b2}
        -> {b1p' : bs ∍ b1'} -> {b2p' : bs ∍ b2'}
        -> (1≠2 : b1p' ≠-∍ b2p')
        -> MiniLink-AF ts b1p b1p' -> MiniLink-AF ts b2p b2p'
        -> (f1 : b1' ⟶ x) -> (f2 : b2' ⟶ x)
        -> ArrowForrest as (rem₂ bs b1p' b2p' 1≠2 ⋆ incl x)
  merge-AF ts 1≠2 l1 l2 f1 f2 =
    let ts1 = ts \\-AF (minilink-Link l2)
    in {!!}


  -- merge-AF : ∀{as bs : ⋆List ℬ}
  --       -> (ts : ArrowForrest as bs)
  --       -> {b1 b2 x : ℬ}
  --       -> {b1p : bs ∍ b1} -> {b2p : bs ∍ b2} -> (1≠2 : b1p ≠-∍ b2p)
  --       -> MicroLink-AF ts b1p -> MicroLink-AF ts b2p
  --       -> (f1 : b1 ⟶ x) -> (f2 : b2 ⟶ x)
  --       -> ArrowForrest as (rem₂ bs b1p b2p 1≠2 ⋆ incl x)
  -- merge-AF ts 1≠2 l1 l2 f1 f2 = {!!}

record isCheckingBoundary (ℬ : Category 𝑖) (F : Functor ℬ (𝐔𝐧𝐢𝐯 𝑗)) : 𝒰 (𝑖 ､ 𝑗) where
  field tryMerge : ∀{b0 b1 : ⟨ ℬ ⟩} -> (v0 : ⟨ F ⟩ b0) (v1 : ⟨ F ⟩ b1)
                   -> Maybe (∑ λ bx -> ∑ λ (f0 : b0 ⟶ bx) -> ∑ λ (f1 : b1 ⟶ bx) -> map f0 v0 ≡ map f1 v1)

open isCheckingBoundary {{...}} public

module _ {ℬ : 𝒰 𝑖} {{_ : isCategory {𝑗} ℬ}} {{_ : isSet-Str ℬ}} {F : Functor ′ ℬ ′ (𝐔𝐧𝐢𝐯 𝑙)} {{_ : isCheckingBoundary ′ ℬ ′ F}}
         (C : 𝒰 𝑘)
       where

  -- data CheckStrategy (cs : ⋆List C) : 𝒰 𝑘 where

  CheckStrategy : 𝒰 _
  CheckStrategy = List (C × C)

  -- data CheckStep : {as bs cs : ⋆List ℬ} (ts : ArrowForrest as bs) (us : ArrowForrest as cs) -> 𝒰 (𝑖 ､ 𝑗) where
  --   incl : ∀{as bs : ⋆List ℬ}
  --        -> (ts : ArrowForrest as bs)
  --        -> {b1 b2 x : ℬ}
  --        -> (b1p : bs ∍ b1) -> (b2p : bs ∍ b2) -> (1≠2 : b1p ≠-∍ b2p)
  --        -> (f1 : b1 ⟶ x) -> (f2 : b2 ⟶ x)
  --        -> CheckStep ts (merge-AF ts 1≠2 f1 f2)

  module _ {as : ⋆List ℬ} (initb : C -> ℬ) (initbo : ∀(c : C) -> as ∍ initb c) (initv : ∀(c : C) -> ⟨ F ⟩ (initb c)) where

    data CheckTree : (s : CheckStrategy) {bs : ⋆List ℬ} (ts : ArrowForrest as bs) -> 𝒰 (𝑘 ､ 𝑖 ､ 𝑗) where
      []   : ∀{bs} -> {ts : ArrowForrest as bs} -> CheckTree [] ts

      skip : ∀{bs} -> {ts : ArrowForrest as bs}
             -> ∀{s} -> CheckTree s ts
             -> ∀{c0 c1}
             -> CheckTree ((c0 , c1) ∷ s) ts

      step : ∀{bs} -> {ts : ArrowForrest as bs}
            -> ∀{s} -> CheckTree s ts
            -> ∀{c0 c1 x b0 b1}
            -> (next0-0 : as ∍ initb c0) -> (next1-0 : as ∍ initb c1)
            -> (next0-1 : bs ∍ b0) -> (next1-1 : bs ∍ b1)
            -> (1≠2 : next0-1 ≠-∍ next1-1)
            -> (f1 : b0 ⟶ x) -> (f2 : b1 ⟶ x)
            -> (l1 : MiniLink-AF ts next0-0 next0-1) -> (l2 : MiniLink-AF ts next1-0 next1-1)
            -> CheckTree ((c0 , c1) ∷ s) (merge-AF ts 1≠2 l1 l2 f1 f2)

    check : (s : CheckStrategy) -> ∑ λ bs -> ∑ λ (ts : ArrowForrest as bs) -> CheckTree s ts
    check ⦋⦌ = as , (id-矢森 , [])
    check ((c0 , c1) ∷ s) =
      let bs , ts , ct = check s
          b0 , bs∍b0 , l0 = getLink ts (initbo c0)
          b1 , bs∍b1 , l1 = getLink ts (initbo c1)
      in case compare-∍ bs∍b0 bs∍b1 of
           (λ b0≠b1 →
              let f0 = linkhom l0
                  f1 = linkhom l1
                  v0' = map f0 (initv c0)
                  v1' = map f1 (initv c1)
              in case tryMerge v0' v1' of
                  (λ _ → _ , (_ , (skip ct)))
                  (λ (bx , f0x , f1x , f0v≡f1v) → _ , (_ , step ct (initbo c0) (initbo c1) bs∍b0 bs∍b1 b0≠b1 f0x f1x l0 l1))
           )
           (λ _ → _ , (_ , (skip ct)))



  -- data Link-AF : {as bs : ⋆List ℬ} -> (ts : ArrowForrest as bs) -> ∀{a} -> (as ∍ a) -> (bs ∍ a) -> 𝒰 (𝑖 ､ 𝑗) where
  --   incl : ∀{as b} -> {ts : ArrowTree as b} -> (as∍b : as ∍ b) -> Link-AF (incl ts) as∍b incl
  --   left-∍ : ∀{as bs cs ds}
  --         -> {ts : ArrowForrest as bs}
  --         -> {us : ArrowForrest cs ds}
  --         -> ∀{x} -> (p0 : as ∍ x) -> (p1 : bs ∍ x)
  --         -> Link-AF ts p0 p1
  --         -> Link-AF (ts ⋆-⧜ us) (left-∍ p0) (left-∍ p1)
  --   right-∍ : ∀{as bs cs ds}
  --         -> {ts : ArrowForrest as bs}
  --         -> {us : ArrowForrest cs ds}
  --         -> ∀{x} -> (p0 : cs ∍ x) -> (p1 : ds ∍ x)
  --         -> Link-AF us p0 p1
  --         -> Link-AF (ts ⋆-⧜ us) (right-∍ p0) (right-∍ p1)


  -- data CheckStep : {as bs cs : ⋆List ℬ} (ts : ArrowForrest as bs) (us : ArrowForrest as cs) -> 𝒰 (𝑖 ､ 𝑗) where
  --   incl : ∀{as bs : ⋆List ℬ}
  --        -> (ts : ArrowForrest as bs)
  --        -> {b1 b2 x : ℬ}
  --        -> (b1p : bs ∍ b1) -> (b2p : bs ∍ b2) -> (1≠2 : b1p ≠-∍ b2p)
  --        -> (f1 : b1 ⟶ x) -> (f2 : b2 ⟶ x)
  --        -> CheckStep ts (merge-AF ts b1p b2p 1≠2 f1 f2)

  -- data CheckTree : (s : CheckStrategy) {as bs cs : ⋆List ℬ} (ts : ArrowForrest as bs) (us : ArrowForrest as cs) -> 𝒰 (𝑘 ､ 𝑖 ､ 𝑗) where
  --   []   : ∀{as bs} -> {ts : ArrowForrest as bs} -> CheckTree [] ts ts
  --   skip : ∀{as bs cs} -> {ts : ArrowForrest as bs} {us : ArrowForrest as cs}
  --          -> ∀{c0 c1 s}
  --          -> CheckTree s ts us -> CheckTree ((c0 , c1) ∷ s) ts us



{-
-}
