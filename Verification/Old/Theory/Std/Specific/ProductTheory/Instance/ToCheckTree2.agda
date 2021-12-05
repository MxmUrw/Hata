
module Verification.Core.Theory.Std.Specific.ProductTheory.Instance.ToCheckTree2 where

open import Verification.Conventions hiding (_⊔_ ; lookup)
open import Verification.Core.Set.Discrete
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
open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Substitution.Property.Base
open import Verification.Core.Theory.Std.Presentation.NGraph.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition


-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.FromString2
open import Verification.Core.Theory.Std.Presentation.CheckTree.Definition2
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.FromANVecTree
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  comm-lookup-map : ∀{f : A -> B} -> ∀{i : Fin-R n} -> ∀{as : Vec A n} -> lookup i (map-Vec f as) ≡ f (lookup i as)
  comm-lookup-map = {!!}


    -- node : (a : A) -> (人Vec VecTree (l a)) -> VecTree
    -- var  : B -> VecTree

-- module _ {A : 𝒰 𝑖} {l : A -> 人ℕ' 𝑖} where
--   data TreeStep1 : (t s : VecTree1 A l) -> 𝒰 𝑖 where

--     incl : ∀{a : A} -> (ts : ([ l a ]ᶠ -> (VecTree1 A l))) -> (i : [ l a ]ᶠ)
--            -> TreeStep1 (node1 a ts) (ts i)

--   data TreePath1 : (t s : VecTree1 A l) -> 𝒰 (𝑖) where
--     [] : ∀{t : VecTree1 A l} -> TreePath1 t t
--     step : ∀{r s t : (VecTree1 A l)} -> TreePath1 r s -> TreeStep1 s t -> TreePath1 r t


--   Vertex1 : (r : VecTree1 A l) -> 𝒰 _
--   Vertex1 r = ∑ TreePath1 r

-- module _ {A : 𝒰 𝑖} {l : A -> ℕ} {ℬ : 𝒰 𝑖} {{_ : isCategory {𝑗} ℬ}} {{_ : isSet-Str ℬ}} {F : Functor ′ ℬ ′ (𝐔𝐧𝐢𝐯 𝑙)} where
--   module _ (b : ℬ) where
--     data isANVecTree : (⟨ F ⟩ b) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙) where
--       node1 : (a : A) -> (Vec VecTree1 (l a)) -> VecTree1


-- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
--   map-Vec : ∀{n} -> (f : A -> B) -> Vec A n -> Vec B n
--   map-Vec = ?

infixl 30 _∙-≡_
_∙-≡_ = trans-Path


module _ {A : 𝒰 𝑖} {l : A -> ℕ} {ℬ : 𝒰 𝑖} {{_ : isCategory {𝑗} ℬ}} {{_ : isSet-Str ℬ}} {F : Functor ′ ℬ ′ (𝐔𝐧𝐢𝐯 𝑙)} {{_ : isCheckingBoundary ′ ℬ ′ F}} where

  module _ (initb : A -> ℬ)
           (initv : ∀(a : A) -> ⟨ F ⟩ (initb a))
           (initvs : ∀(a : A) -> Vec (⟨ F ⟩ (initb a)) (l a))
           (WT : ∀{b} -> (a : A) -> ⟨ F ⟩ b -> Vec (⟨ F ⟩ b) (l a) -> 𝒰 𝑘)
           where

    -- ADANVecTree1 : 
    ADANVecTree1 = ADANVecTree A l ℬ F WT

    mutual
      makeInitialTrees : ∀{n} -> Vec (VecTree1 A l) n -> Vec (∑ ADANVecTree A l ℬ F WT) n
      makeInitialTrees ⦋⦌ = ⦋⦌
      makeInitialTrees (x ∷ ts) = (makeInitialTree x) ∷ (makeInitialTrees ts)

      makeInitialTree : VecTree1 A l -> ∑ ADANVecTree A l ℬ F WT
      makeInitialTree (node1 a x) = _ , (node1 a (initb a) (initv a) (initvs a) {!!} (makeInitialTrees x))

    mutual
      ibounds : ⋆List ℬ -> Vec (∑ ADANVecTree1) n -> ⋆List ℬ
      ibounds ac ⦋⦌ = ac
      ibounds ac (x ∷ v) = ibounds (ac ⋆ ibound x) v

      ibound : ∑ ADANVecTree1 -> ⋆List ℬ
      ibound (_ , node1 a b _ _ _ x) = ibounds (incl b) x

    private
      lem-1 : ∀{a} -> {ac : ⋆List ℬ} -> (ts : Vec (∑ ADANVecTree1) n) -> ac ∍ a -> ibounds ac ts ∍ a
      lem-1 ⦋⦌ p = p
      lem-1 (x ∷ ts) p = lem-1 ts (left-∍ p)

      lem-1' : (t : ∑ ADANVecTree1) -> ibound t ∍ (t .fst .fst)
      lem-1' (_ , node1 a _ _ _ _ x) = lem-1 x incl

      lem-2 : ∀{a} -> {ac : ⋆List ℬ} -> (ts : Vec (∑ ADANVecTree1) n) -> (i : Fin-R n) -> ibound (lookup i ts) ∍ a -> ibounds ac ts ∍ a
      lem-2 (x ∷ ts) zero p = lem-1 ts (right-∍ p)
      lem-2 (x ∷ ts) (suc i) p = lem-2 ts i p


    mutual
      appendStrategy : ∀{as a} -> (s : Strategy as) -> (as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (v : Vec (∑ ADANVecTree1) n) -> Strategy (ibounds as v)
      appendStrategy s as∍a ⦋⦌ ⦋⦌ = s
      appendStrategy s as∍a (v ∷ vs) (t@((tb , tv) , ttree) ∷ ts) =
        let tstrat = makeStrategy t
        in appendStrategy (resolve s tstrat (rtarget _ as∍a v , rtarget tb (lem-1' t) tv)) (left-∍ as∍a) vs ts

      makeStrategy : (v : ∑ ADANVecTree1) -> Strategy (ibound v)
      makeStrategy (_ , node1 a b v vs _ x) = appendStrategy (begin b) incl vs x -- , rt1


{-
    isValidStrategy1 : ∀{as b} -> (t : ADANVecTree A l ℬ F WT b) -> (s : Strategy as) -> 𝒰 _
    isValidStrategy1 {as} {b} t _ = ∀{b1} -> (v1 : ⟨ F ⟩ b1) -> (ADANVertex A l ℬ F WT) v1 (_ , t) -> as ∍ b1

    isValidStrategy2 : ∀{as b} -> (t : ADANVecTree A l ℬ F WT b) -> (s : Strategy as) -> 𝒰 _
    isValidStrategy2 t s = ∀{b1 b2} -> (v1 : ⟨ F ⟩ b1) (v2 : ⟨ F ⟩ b2) (vout : ⟨ F ⟩ b1)-> (ADANEdge A l ℬ F WT) v1 v2 vout (_ , t) -> s ∍-St₂ (rtarget b1 vout , rtarget b2 v2)

    isValidStrategy3₀ : ∀{as b} -> (t : ADANVecTree A l ℬ F WT b) -> (s : Strategy as)
                       -> (valid1 : isValidStrategy1 t s) -> (valid2 : isValidStrategy2 t s) -> 𝒰 _
    isValidStrategy3₀ t s valid1 valid2 = ∀{b1 b2} -> (v1 : ⟨ F ⟩ b1) (v2 : ⟨ F ⟩ b2) (vout : ⟨ F ⟩ b1)-> (e : (ADANEdge A l ℬ F WT) v1 v2 vout (_ , t))
                                 -> getElemSt₀ (valid2 v1 v2 vout e) ≡ valid1 v1 (e .fst , e .snd .snd .fst)

    isValidStrategy3₁ : ∀{as b} -> (t : ADANVecTree A l ℬ F WT b) -> (s : Strategy as)
                       -> (valid1 : isValidStrategy1 t s) -> (valid2 : isValidStrategy2 t s) -> 𝒰 _
    isValidStrategy3₁ t s valid1 valid2 = ∀{b1 b2} -> (v1 : ⟨ F ⟩ b1) (v2 : ⟨ F ⟩ b2) (vout : ⟨ F ⟩ b1)-> (e : (ADANEdge A l ℬ F WT) v1 v2 vout (_ , t))
                                 -> getElemSt₁ (valid2 v1 v2 vout e) ≡ valid1 v2 ((e .snd .fst) , (step (e .snd .snd .fst) (e .snd .snd .snd))) -- (e .fst , e .snd .snd .fst)
                                 -}

    -- we show that `makeStrategy` creates a valid strategy

    module myproofs1 where


      Pstep : ∀{b} -> {t s : ∑ ADANVecTree1}
                    -> ∀{vout}
                    -> ADANTreeStep A l ℬ F WT (t) (s) vout
                    -> ibound s ∍ b -> ibound t ∍ b
      Pstep (incl a b v vs wt ts i) bp = lem-2 ts i bp

      Ppath : ∀{b} -> {t s : ∑ ADANVecTree1}
                    -> ADANTreePath A l ℬ F WT (t) (s)
                    -> ibound s ∍ b -> ibound t ∍ b
      Ppath [] bp = bp
      Ppath (step p x) bp = Ppath p (Pstep x bp)

      P : ∀{t s : ∑ ADANVecTree1} -> ADANTreePath A l ℬ F WT t s -> ibound t ∍ s .fst .fst
      P {t = t} {s} p = Ppath p (lem-1' s)

      -- about edges
      map-append : ∀{as a} -> {s : Strategy as} -> {p : as ∍ a} -> {vs : Vec (⟨ F ⟩ a) n} -> {ts : Vec (∑ ADANVecTree1) n}
                   -> (rp : ResolutionPair₂)
                   -> s ∍-St₂ rp
                   -> appendStrategy s p vs ts ∍-St₂ rp
      map-append {vs = ⦋⦌} {⦋⦌} rp p = p
      map-append {vs = x ∷ vs} {x₁ ∷ ts} rp p = map-append {vs = vs} {ts} rp (left-∍ p)



      P1s : ∀{as a} -> {s : Strategy as} -> {p : as ∍ a} -> (vs : Vec (⟨ F ⟩ a) n) -> (ts : Vec (∑ ADANVecTree1) n)
            -> (i : Fin-R n)
            -> appendStrategy s p vs ts ∍-St₂
                (rtarget a (lookup i vs) ,
                rtarget (lookup i ts .fst .fst) (lookup i ts .fst .snd))
      P1s {as = as} {a} {s = s} {p} (x ∷ vs) (t@((tb , tv) , ttree) ∷ ts) zero = map-append {vs = vs} {ts = ts} _ (incl _ _ p (lem-1' t) x tv)
      P1s {s = s} (x ∷ vs) (t@((tb , tv) , node1 a .tb .tv vs₁ x₁ x₂) ∷ ts) (suc i) = P1s vs ts i




      lem-4 : ∀{as a} -> (s : Strategy as) -> (p : as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (ts : Vec (∑ ADANVecTree1) n)
                   -> (rp : ResolutionPair₂)
                   -> (i : Fin-R n)
                   -> makeStrategy (lookup i ts) ∍-St₂ rp
                   -> appendStrategy s p vs ts ∍-St₂ rp
      lem-4 s p (x ∷ vs) (t ∷ ts) rp zero sp = map-append {vs = vs} {ts = ts} _ (right-∍ sp)
      lem-4 s p (x ∷ vs) (x₁ ∷ ts) rp (suc i) sp = lem-4 _ _ vs ts rp i sp


      P1 : {t s : ∑ ADANVecTree1} -> ∀{vout} -> ADANTreeStep A l ℬ F WT t s vout -> makeStrategy t ∍-St₂ ((rtarget _ vout) , (rtarget (s .fst .fst) (s .fst .snd)))
      P1 (incl a b v vs wt ts i) = P1s vs ts i

      P1step : {t s : ∑ ADANVecTree1} -> ∀{vout} -> ADANTreeStep A l ℬ F WT t s vout
               -> ∀{rp : ResolutionPair₂} -> makeStrategy s ∍-St₂ rp -> makeStrategy t ∍-St₂ rp
      P1step (incl a b v vs wt ts i) {rp} sp = lem-4 (begin b) incl vs ts rp i sp

{-
      P1path : {t s : ∑ ADANVecTree1} -> ADANTreePath A l ℬ F WT t s
               -> ∀{rp : ResolutionPair₂} -> makeStrategy s ∍-St₂ rp -> makeStrategy t ∍-St₂ rp
      P1path [] P = P
      P1path (step pat x) P = P1path pat (P1step x P)

      -- lem-1₀ : ∀{a} -> {ac : ⋆List ℬ} -> {ts : Vec (∑ ADANVecTree1) n} -> {ac ∍ a} -> ibounds ac ts ∍ a


      lem-1₀ : ∀{as a} -> (s : Strategy as)
                    -> (p : as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (ts : Vec (∑ ADANVecTree1) n)
                   -> (rp : ResolutionPair₂)
                   -> {sep : s ∍-St₂ rp}
                   -> {bop : as ∍ rp .fst .fst}
                   -> getElemSt₀ sep ≡ bop
                   -> getElemSt₀ (map-append {s = s} {p = p} {vs = vs} {ts = ts} rp (sep)) ≡ lem-1 ts (bop)
      lem-1₀ s p ⦋⦌ ⦋⦌ rp sepbop = sepbop
      lem-1₀ s p (x ∷ vs) (x₁ ∷ ts) rp sepbop = lem-1₀ _ _ vs ts rp (cong left-∍ sepbop) -- sepbop

-}

      lem-1₁ : ∀{as a} -> (s : Strategy as)
                    -> (p : as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (ts : Vec (∑ ADANVecTree1) n)
                   -> (rp : ResolutionPair₂)
                   -> {sep : s ∍-St₂ rp}
                   -> {bop : as ∍ rp .snd .fst}
                   -> getElemSt₁ sep ≡ bop
                   -> getElemSt₁ (map-append {s = s} {p = p} {vs = vs} {ts = ts} rp (sep)) ≡ lem-1 ts (bop)
      lem-1₁ s p ⦋⦌ ⦋⦌ rp sepbop = sepbop
      lem-1₁ s p (x ∷ vs) (x₁ ∷ ts) rp sepbop = lem-1₁ _ _ vs ts rp (cong left-∍ sepbop) -- sepbop

      -- lem-1u : ∀{as a} -> (s : Strategy as)
      --               -> (p : as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (ts : Vec (∑ ADANVecTree1) n)
      --              -> (rp : ResolutionPair₂)
      --              -> {sep : s ∍-St₂ rp}
      --              -> getElemSt₀ (map-append {s = s} {p = p} {vs = vs} {ts = ts} rp (sep)) ≡ lem-1 ts (getElemSt₀ sep)
      -- lem-1u s p ⦋⦌ ⦋⦌ rp sepbop = sepbop
      -- lem-1u s p (x ∷ vs) (x₁ ∷ ts) rp sepbop = lem-1₀ _ _ vs ts rp (cong left-∍ sepbop) -- sepbop

{-
      lem-42₀ : ∀{as a} -> (s : Strategy as) -> (p : as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (ts : Vec (∑ ADANVecTree1) n)
                   -> (rp : ResolutionPair₂)
                   -> (i : Fin-R n)
                   -> {sep : makeStrategy (lookup i ts) ∍-St₂ rp}
                   -> {bop : ibound (lookup i ts) ∍ rp .fst .fst}
                   -> getElemSt₀ sep ≡ bop
                   -> getElemSt₀ (lem-4 s p vs ts rp i sep) ≡ lem-2 ts i bop
      lem-42₀ s p (x ∷ vs) (x₁ ∷ ts) rp zero sepbop = lem-1₀ _ _ vs ts rp (cong right-∍ sepbop) -- sepbop
      lem-42₀ s p (x ∷ vs) (x₁ ∷ ts) rp (suc i) sepbop = lem-42₀ _ _ vs ts rp i sepbop

-}
      lem-42₁ : ∀{as a} -> (s : Strategy as) -> (p : as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (ts : Vec (∑ ADANVecTree1) n)
                   -> (rp : ResolutionPair₂)
                   -> (i : Fin-R n)
                   -> {sep : makeStrategy (lookup i ts) ∍-St₂ rp}
                   -> {bop : ibound (lookup i ts) ∍ rp .snd .fst}
                   -> getElemSt₁ sep ≡ bop
                   -> getElemSt₁ (lem-4 s p vs ts rp i sep) ≡ lem-2 ts i bop
      lem-42₁ s p (x ∷ vs) (x₁ ∷ ts) rp zero sepbop = lem-1₁ _ _ vs ts rp (cong right-∍ sepbop) -- sepbop
      lem-42₁ s p (x ∷ vs) (x₁ ∷ ts) rp (suc i) sepbop = lem-42₁ _ _ vs ts rp i sepbop

{-
      lem-step : {t s : ∑ ADANVecTree1} -> ∀{vout} -> (pat : ADANTreeStep A l ℬ F WT t s vout)
               -> ∀{rp : ResolutionPair₂} -> {sep : makeStrategy s ∍-St₂ rp}
               -> {bop : ibound s ∍ rp .fst .fst}
               -> getElemSt₀ sep ≡ bop
               -> getElemSt₀ (P1step pat sep) ≡  (Pstep pat bop)
      lem-step (incl a b v vs wt ts i) {rp} p = lem-42₀ (begin b) incl vs ts rp i p


      lem-path : {t s : ∑ ADANVecTree1} -> (pat : ADANTreePath A l ℬ F WT t s)
               -> ∀{rp : ResolutionPair₂} -> {sep : makeStrategy s ∍-St₂ rp}
               -> {bop : ibound s ∍ rp .fst .fst}
               -> getElemSt₀ sep ≡ bop
               -> getElemSt₀ (P1path pat sep) ≡  (Ppath pat bop)
      lem-path [] p = p
      lem-path (step pat x) p = lem-path pat (lem-step x p)


      lem-step₁ : {t s : ∑ ADANVecTree1} -> ∀{vout} -> (pat : ADANTreeStep A l ℬ F WT t s vout)
               -> ∀{rp : ResolutionPair₂} -> {sep : makeStrategy s ∍-St₂ rp}
               -> {bop : ibound s ∍ rp .snd .fst}
               -> getElemSt₁ sep ≡ bop
               -> getElemSt₁ (P1step pat sep) ≡  (Pstep pat bop)
      lem-step₁ (incl a b v vs wt ts i) sepbop = lem-42₁ (begin b) incl vs ts _ i sepbop
-}
{-
      lem-path₁ : {t s : ∑ ADANVecTree1} -> (pat : ADANTreePath A l ℬ F WT t s)
               -> ∀{rp : ResolutionPair₂} -> {sep : makeStrategy s ∍-St₂ rp}
               -> {bop : ibound s ∍ rp .snd .fst}
               -> getElemSt₁ sep ≡ bop
               -> getElemSt₁ (P1path pat sep) ≡  (Ppath pat bop)
      lem-path₁ [] p = p
      lem-path₁ (step pat x) p = lem-path₁ pat (lem-step₁ x p)


      -- same-path : {t s : ∑ ADANVecTree1} -> (p : ADANTreePath A l ℬ F WT t s) -> ∀{rp : ResolutionPair₂}
      --             -> (sp : makeStrategy s ∍-St₂ rp) -> getElemSt₀ (P1path p sp) ≡ P 
      -- same-path p 

      -- same-1 : {t2 t3 : ∑ ADANVecTree1} -> ∀{vout} -> (p : ADANTreeStep A l ℬ F WT t2 t3 vout) -> ∀{rp : ResolutionPair₂}
      --             -> (getElemSt₀ (P1 p) ≡ lem-1' t2) × (getElemSt₁ (P1 p) ≡ lem-1' ({!!} , {!t3 .snd!}))
      -- same-1 (incl a b v vs wt ts i) = {!!}

    module _ (t : ∑ ADANVecTree1) where
      valid1:makeStrategy : isValidStrategy1 (t .snd) (makeStrategy t)
      valid1:makeStrategy v1 (s , vert) = myproofs1.P vert

      valid2:makeStrategy : isValidStrategy2 (t .snd) (makeStrategy t)
      valid2:makeStrategy v1 v2 vout (t2 , t3 , pat , ed) = myproofs1.P1path pat (myproofs1.P1 ed)

      isValidStrategy3₀:makeStrategy : ∀{b1 b2} -> (v1 : ⟨ F ⟩ b1) (v2 : ⟨ F ⟩ b2) (vout : ⟨ F ⟩ b1)-> (e : (ADANEdge A l ℬ F WT) v1 v2 vout t)
                                  -> getElemSt₀ (valid2:makeStrategy v1 v2 vout e) ≡ valid1:makeStrategy v1 (e .fst , e .snd .snd .fst)
      isValidStrategy3₀:makeStrategy v1 v2 vout (t1 , t2 , p , ed) = myproofs1.lem-path p {!!}


      isValidStrategy3₁:makeStrategy : ∀{b1 b2} -> (v1 : ⟨ F ⟩ b1) (v2 : ⟨ F ⟩ b2) (vout : ⟨ F ⟩ b1)-> (e : (ADANEdge A l ℬ F WT) v1 v2 vout t)
                                     -> getElemSt₁ (valid2:makeStrategy v1 v2 vout e) ≡ valid1:makeStrategy v2 ((e .snd .fst) , (step (e .snd .snd .fst) (e .snd .snd .snd)))
      isValidStrategy3₁:makeStrategy v1 v2 vout (t1 , t2 , p , ed)= myproofs1.lem-path₁ p {!!}

-}

{-
{-

{-
    module _ {as tb} (t : ADANVecTree A l ℬ F WT tb) (s : Strategy as)
             (valids : isValidStrategy1 t s) (valids2 : isValidStrategy2 t s)
             (valids30 : isValidStrategy3₀ t s valids valids2)
             (valids31 : isValidStrategy3₁ t s valids valids2)
             {bx} (ex : Execution s bx) (exCorrect : isCorrect ex) where


      mutual
        makeFinalTrees : ∀{n} -> (ts : Vec (∑ ADANVecTree A l ℬ F WT) n) -> (vs : Vec (⟨ F ⟩ bx) n)
                              -> (p : ∀(i : Fin-R n) -> ADANTreePath A l ℬ F WT (_ , t) (lookup i ts))

                              -> (∀(i : Fin-R n) -> map (execHom ex
                                                                 (valids (lookup i ts .fst .snd)
                                                                         (lookup i ts .snd , p i)))
                                                        (lookup i ts .fst .snd)
                                                    ≡
                                                    lookup i vs
                                 )
                              -> DVec (ANVecTree A l ℬ F WT bx) vs
        makeFinalTrees ⦋⦌ ⦋⦌ ps pP = []
        makeFinalTrees ((_ , t) ∷ ts) (v ∷ vs) ps pP = t1 ∷ (makeFinalTrees ts vs (λ i -> ps (suc i)) (λ i -> pP (suc i)))
          where
            t0 = makeFinalTree _ t (ps zero)

            t1 : ANVecTree A l ℬ F WT bx v
            t1 = transport (λ i -> ANVecTree A l ℬ F WT bx (pP zero i)) t0


        makeFinalTree : ∀{b0} -> (vb0 : ⟨ F ⟩ b0) (s : ADANVecTree A l ℬ F WT (b0 , vb0)) -> (p : ADANTreePath A l ℬ F WT (_ , t) (_ , s)) -> ANVecTree A l ℬ F WT bx (map (execHom ex (valids vb0 (s , p))) vb0)
        makeFinalTree {b0} vb0 curtree@(node1 a .b0 .vb0 vs wt ts) p = (node1 a (map f0 vb0) (map-Vec (map f0) vs) {!!} ts')
          where
            sb∍b : as ∍ b0
            sb∍b = (valids vb0 (((node1 a b0 vb0 vs wt ts)) , p))

            f0 : b0 ⟶ bx
            f0 = execHom ex sb∍b

            getEdge : ∀(i : Fin-R (l a)) -> ADANEdge A l ℬ F WT vb0 (lookup i ts .fst .snd) (lookup i vs) (_ , t)
            getEdge i = ((node1 a b0 vb0 vs wt ts)) , (lookup i ts .snd , p , (incl a b0 vb0 vs wt ts i))

            rtarget∍ : ∀(i : Fin-R (l a)) -> s ∍-St₂ (rtarget _ (lookup i vs) , rtarget _ (lookup i ts .fst .snd))
            rtarget∍ i = valids2 _ _ _ (getEdge i)

            lem-02 : ∀(i : Fin-R (l a))
                    -> map (execHom ex (getElemSt₀ (rtarget∍ i))) (lookup i vs) ≡ map (execHom ex (getElemSt₁ (rtarget∍ i))) (lookup i ts .fst .snd)
            lem-02 i = exCorrect _ (rtarget∍ i)

            lem-03 :  ∀(i : Fin-R (l a))
                    -> map (execHom ex (valids vb0 (curtree , p))) (lookup i vs) ≡ map (execHom ex (getElemSt₀ (rtarget∍ i))) (lookup i vs)
            lem-03 i = λ j -> map (execHom ex (valids30 _ _ _ (getEdge i) (~ j))) (lookup i vs)

            lem-04 : ∀(i : Fin-R (l a)) ->
                   map (execHom ex
                    (valids (lookup i ts .fst .snd)
                      (lookup i ts .snd , step p (incl a b0 vb0 vs wt ts i))))
                    (lookup i ts .fst .snd)
                    ≡
                    map (execHom ex (getElemSt₁ (rtarget∍ i)))
                    (lookup i ts .fst .snd)
            lem-04 i = λ j -> map (execHom ex (valids31 _ _ _ (getEdge i) (~ j))) (lookup i ts .fst .snd)

            ts' : DVec (ANVecTree A l ℬ F WT bx) _
            ts' = makeFinalTrees ts (map-Vec (map f0) vs) (λ i → step p (incl a b0 vb0 vs wt ts i)) (λ i → lem-04 i ∙-≡ sym-Path (lem-02 i) ∙-≡ sym-Path (lem-03 i) ∙-≡ sym-Path (comm-lookup-map  {i = i}))

-}
-}
-}
