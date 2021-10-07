
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.ToCheckTree2 where

open import Verification.Conventions hiding (_⊔_ ; lookup)
open import Verification.Experimental.Set.Discrete
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
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Substitution.Property.Base
open import Verification.Experimental.Theory.Std.Presentation.NGraph.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition


-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString2
open import Verification.Experimental.Theory.Std.Presentation.CheckTree.Definition2
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromANVecTree



module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  comm-lookup-map : ∀{f : A -> B} -> ∀{i : Fin-R n} -> ∀{as : Vec A n} -> lookup i (map-Vec f as) ≡ f (lookup i as)
  comm-lookup-map = {!!}


module _ (A : 𝒰 𝑖) (l : A -> ℕ) where
  data VecTree1 : 𝒰 (𝑖) where
    node1 : (a : A) -> (Vec VecTree1 (l a)) -> VecTree1
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

    mutual
      makeInitialTrees : ∀{n} -> Vec (VecTree1 A l) n -> Vec (∑ ADANVecTree A l ℬ F WT) n
      makeInitialTrees ⦋⦌ = ⦋⦌
      makeInitialTrees (x ∷ ts) = (makeInitialTree x) ∷ (makeInitialTrees ts)

      makeInitialTree : VecTree1 A l -> ∑ ADANVecTree A l ℬ F WT
      makeInitialTree (node1 a x) = _ , (node1 a (initb a) (initv a) (initvs a) {!!} (makeInitialTrees x))

    mutual
      ibounds : 人List ℬ -> Vec (VecTree1 A l) n -> 人List ℬ
      ibounds ac ⦋⦌ = ac
      ibounds ac (x ∷ v) = ibounds (ac ⋆ ibound x) v

      ibound : VecTree1 A l -> 人List ℬ
      ibound (node1 a x) = ibounds (incl (initb a)) x

    private
      lem-1 : ∀{a} -> {ac : 人List ℬ} -> (ts : Vec (VecTree1 A l) n) -> ac ∍ a -> ibounds ac ts ∍ a
      lem-1 ⦋⦌ p = p
      lem-1 (x ∷ ts) p = lem-1 ts (left-∍ p)

    mutual
      appendStrategy : ∀{as a} -> (s : Strategy as) -> (as ∍ a) -> (vs : Vec (⟨ F ⟩ a) n) -> (v : Vec (VecTree1 A l) n) -> Strategy (ibounds as v)
      appendStrategy s as∍a ⦋⦌ ⦋⦌ = s
      appendStrategy s as∍a (v ∷ vs) (t ∷ ts) =
        let tstrat , trt = makeStrategy t
        in appendStrategy (resolve s tstrat (rtarget _ as∍a v , trt)) (left-∍ as∍a) vs ts

      makeStrategy : (v : VecTree1 A l) -> (Strategy (ibound v) × ResolutionTarget (ibound v))
      makeStrategy (node1 a x) = appendStrategy (begin (initb a)) incl (initvs a) x , rt1
        where
          init∍b : ibounds (incl (initb a)) x ∍ (initb a)
          init∍b = lem-1 x incl

          rt1 : ResolutionTarget (ibounds (incl (initb a)) x)
          rt1 = rtarget _ (init∍b) (initv a)


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

    -- we show that `makeStrategy` creates a valid strategy

    module _ (t : VecTree1 A l) where
      valid1:makeStrategy : isValidStrategy1 (makeInitialTree t .snd) (makeStrategy t .fst)
      valid1:makeStrategy = P t
        where
          -- ibounds : 人List ℬ -> Vec (VecTree1 A l) n -> 人List ℬ
          -- (t : VecTree1 A l) -> ∀{b1} -> (v1 : ⟨ F ⟩ b1) -> (ADANVertex A l ℬ F WT) v1 (makeInitialTree t) -> ibound t ∍ b1

          Ps0 : {ac : 人List ℬ} -> ∀{a} -> (ac ∍ a) -> (ts : Vec (VecTree1 A l) n) -> ibounds (ac) ts ∍ a
          Ps0 p ⦋⦌ = p
          Ps0 p (x ∷ ts) = Ps0 (left-∍ p) ts

          Ps : {ac : 人List ℬ} -> ∀{b1} -> (ts : Vec (VecTree1 A l) n) -> (i : Fin-R n) -> ibounds ac ts ∍ b1
          Ps t = {!!}

          P0 : (t : VecTree1 A l) -> ibound t ∍ (makeInitialTree t .fst .fst)
          P0 (node1 a x) = Ps0 incl x

          -- Pstep : ∀{b} -> (t s : VecTree1 A l) -> ∀{vout}
          --              -> ADANTreeStep A l ℬ F WT (makeInitialTree t) (makeInitialTree s) vout
          --              -> ibound s ∍ b -> ibound t ∍ b

          Pstep : ∀{b} -> (t' s' : ∑ ADANVecTree A l ℬ F WT)
                       -> (t s : VecTree1 A l)
                       -> (makeInitialTree t ≡ t') -> (makeInitialTree s ≡ s')
                       -> ∀{vout}
                       -> ADANTreeStep A l ℬ F WT (t') (s') vout
                       -> ibound s ∍ b -> ibound t ∍ b
          Pstep .((b , v) , node1 a b v vs wt ts) .(lookup i ts) t s ptt pss (incl a b v vs wt ts i) bm = {!!}

          P : (t : VecTree1 A l) -> ∀{b1} -> (v1 : ⟨ F ⟩ b1) -> (ADANVertex A l ℬ F WT) v1 (makeInitialTree t) -> ibound t ∍ b1
          P (node1 a x) .(snd (fst (makeInitialTree (node1 a x)))) (.(snd (makeInitialTree (node1 a x))) , []) = Ps0 incl x
          P (node1 a ts) v1 (t-next , step p s) = {!!}
          -- Ps ts {!!}


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

