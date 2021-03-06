
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Instance.LogicalFramework where

open import Verification.Core.Conventions hiding (Structure ; _β)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Order.Lattice
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.LogicalFramework.Definition
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition


module _ {π : π° π} {{_ : isCategory {π} π}} where
  infixr 10 _βΆβ¨_β©_
  _βΆβ¨_β©_ : β(a : π) {b c : π} -> (Ο : a βΆ b) -> (Ο : b βΆ c ) -> a βΆ c
  _βΆβ¨_β©_ _ Ο Ο = Ο β Ο

  _βΆid : β(a : π) -> a βΆ a
  _βΆid a = id


pattern makeβi' a b = makeβi {a} {{b}}
pattern since' a b c = β² a β² {b} {{c}}

private
  module _ {K : Kinding πβ} where
    U : CwJ K (π , πβ , π) -> MetaTermCalculus K _
    U π = record {TermCon = JHom}



    F : β{π} -> MetaTermCalculus K π -> CwJ K _
    F Ξ³ = MTCCat Ξ³ since (isCwJ:MTCCat {Ξ³ = Ξ³})
      where open MTCDefinitions Ξ³


  -- module MTC-Ξ»β {π : π} {K : Kinding π} {Ξ³ : MetaTermCalculus K π}
  --        {β³ : CwJ K (π , _ , π)}
  --        (Ο : Hom Ξ³ (U β³)) where

module MTC-Ξ»β {π : π} {K : Kinding π} {Ξ³ : MetaTermCalculus K π}
        {β³ : π° πβ}
        {{oCategory : isCategory {πβ} β³}}
        {{oMonoidal : isMonoidal β² β³ β²}}
        {{pβ³       : isCwJ K β² β³ β²}}
        -- {β³ : CwJ K π}
        (Ο : Hom-MTC Ξ³ (U β² β³ β²)) where


    private

  -- i : β{K : Kinding π} {Ξ³ : MetaTermCalculus K (π)} -> β {β³} -> (Hom Ξ³ (U β³)) -> (Hom (F Ξ³) β³)
  -- i {Ξ³ = Ξ³} {since' β³ (oβ³) pβ³} Ο = f since isFunctor:f -- 18 sek instance search w/o spec | 14 with spec
  -- i {Ξ³ = Ξ³} {since' β³ (makeβi {makeβi {oCat}}) pβ³} Ο = f since isFunctor:f

      -- pβ³ = of β³
      -- oβ³ = _:&_.oldProof β³
      -- oMonoidal = βi_.isnd oβ³
      -- oCategory = βi_.isnd (βi_.ifst oβ³)
      oMonoid = isMonoidal.isMonoid:this oMonoidal

      instance
        _ : isSetoid β³
        _ = isSetoid:byCategory

      open MTCDefinitions Ξ³

      f : β¨ F Ξ³ β© -> β³
      f (incl x) = β¦ x β§

      id' : β{a : β³} -> a βΆ a
      id' = id -- {{oCategory}}
      -- {{βi_.isnd (βi_.ifst oβ³)}}

      infixr 10 _βΆ'β¨_β©_
      _βΆ'β¨_β©_ : β(a : β³) {b c : β³} -> (Ο : a βΆ b) -> (Ο : b βΆ c ) -> a βΆ c
      _βΆ'β¨_β©_ a Ο Ο = _β_ Ο Ο
      -- _βΆ'β¨_β©_ a Ο Ο = _β_ {{oCategory}} Ο Ο

      _βΆid' : β(a : β³) -> a βΆ a
      _βΆid' a = id -- {{oCategory}}
      -- _βΆid' a = id {{oCategory}}

      _β'_ : β{A : π° β} -> List A -> List A -> List A
      _β'_ = _++-List_

      -- {{βi_.isnd (βi_.ifst oβ³)}} Ο Ο

      infixl 70 _β'_ _βββ'_
      _βββ'_ : β{a b c d : β³} -> (f : a βΆ b) (g : c βΆ d) -> (a β c βΆ b β d)
      _βββ'_ = Ξ»β (map)

      _β'_ : β³  -> β³  -> β³ 
      _β'_ = _β_ -- {{isMonoidal.isMonoid:this oMonoidal}}


      mutual

        map-fβ : β{π Ξ Ξ Ξ±} ->
                π β©αΆ  (Ξ β£ Ξ β Ξ±)
                -> Hom (β¦ Ξ β§-LK β' β¦ (π β' Ξ) β§-LCJ) (β¦ Ξ β§-LK β' β¦ Ξ± β§-CJ)
        map-fβ (meta {Ξ±s} {Ξ±}) = (id' βββ' β¨ unit-r-β β©)

        map-fβ {π} {Ξ} {Ξ} {Ξ±} (app {πβ} {πβ} {π§ = π§} t s) =
          let t' = map-fβ t
              s' = map-fβ s
          in  {-  β¦ Ξ β§-LK β' β¦ (πβ β' πβ) β' Ξ β§-LCJ                 -} _ βΆ'β¨ map (id' , β¨ ββ¦β§β (assoc-l-β {a = πβ} {πβ} {Ξ}) β©) β©
              {-  β¦ Ξ β§-LK β' β¦ πβ β' (πβ β' Ξ) β§-LCJ                 -} _ βΆ'β¨ id' βββ' β¨ β¦ββ§ {Ξ = πβ} {Ξ = πβ β' Ξ} β© β©
              {-  β¦ Ξ β§-LK β' (β¦ πβ β§-LCJ β' β¦ πβ β' Ξ β§-LCJ)         -} _ βΆ'β¨ β¨ assoc-l-β {{oMonoid}} β»ΒΉ β© β©
              {-  β¦ Ξ β§-LK β' β¦ πβ β§-LCJ β' β¦ πβ β' Ξ β§-LCJ           -} _ βΆ'β¨ id' βββ' β¨ ββ¦β§β (unit-r-β {a = πβ} β»ΒΉ) β© βββ' id' β©
              {-  β¦ Ξ β§-LK β' β¦ πβ β' [] β§-LCJ β' β¦ πβ β' Ξ β§-LCJ     -} _ βΆ'β¨ s' βββ' id' β©
              {-  β¦ Ξ β§-LK β' β¦ π§ β§-CJ β' β¦ πβ β' Ξ β§-LCJ             -} _  βΆ'β¨ id' βββ' β¨ β¦ββ§ {Ξ = πβ} {Ξ = Ξ} β© β©
              {-  β¦ Ξ β§-LK β' β¦ π§ β§-CJ β' (β¦ πβ β§-LCJ β' β¦ Ξ β§-LCJ)   -} _  βΆ'β¨ β¨ assoc-l-β {{oMonoid}} β© β©
              {-  β¦ Ξ β§-LK β' (β¦ π§ β§-CJ β' (β¦ πβ β§-LCJ β' β¦ Ξ β§-LCJ)) -} _  βΆ'β¨ id' βββ' β¨ assoc-l-β {{oMonoid}} β»ΒΉ β© β©
              {-  β¦ Ξ β§-LK β' ((β¦ π§ β§-CJ β' β¦ πβ β§-LCJ) β' β¦ Ξ β§-LCJ) -} _  βΆ'β¨ id' βββ' (braid {{pβ³}} βββ' id') β©
              {-  β¦ Ξ β§-LK β' ((β¦ πβ β§-LCJ β' β¦ π§ β§-CJ) β' β¦ Ξ β§-LCJ) -} _  βΆ'β¨ id' βββ' β¨ assoc-l-β {{oMonoid}} β© β©
              {-  β¦ Ξ β§-LK β' (β¦ πβ β§-LCJ β' (β¦ π§ β§-CJ β' β¦ Ξ β§-LCJ)) -} _  βΆ'β¨ id' βββ' (id' βββ' (β¨ unit-r-β {{oMonoid}} β»ΒΉ β© βββ' id') ) β©
              {-  β¦ Ξ β§-LK β' (β¦ πβ β§-LCJ β' (β¦ π§ β· [] β§-LCJ β' β¦ Ξ β§-LCJ)) -} _  βΆ'β¨ id' βββ' (id' βββ' β¨ β¦ββ§ {Ξ = π§ β· []} {Ξ = Ξ} β»ΒΉ β© ) β©
              {-  β¦ Ξ β§-LK β' (β¦ πβ β§-LCJ β' (β¦ π§ β· Ξ β§-LCJ))          -} _ βΆ'β¨ id' βββ' β¨ β¦ββ§ {Ξ = πβ} {Ξ = π§ β· Ξ} β»ΒΉ β© β©
              {-  β¦ Ξ β§-LK β' (β¦ πβ β' (π§ β· Ξ) β§-LCJ)                 -} _  βΆ'β¨ t' β©
                β¦ Ξ β§-LK β' β¦ Ξ± β§-CJ                                  βΆid


        map-fβ (con {Ξ} {Ξ} {Ξ±} x) =
          let x' = β¨ Ο β© x
          in id' βββ' x'

        map-fβ {π} {Ξ} {Ξ} {Ξ±} (lam {πβ} {πβ} {Ξ± = Ξ±'} {Ξ±s = Ξ±s'} {Ξ²} v x) =
          let x' = map-fβ x
              v' = map-fβ v
              P  = β¦ Ξ β§-LK β' β¦ (πβ β' πβ) β' Ξ β§-LCJ                βΆ'β¨ map (id' , β¨ ββ¦β§β (assoc-l-β {a = πβ} {πβ} {Ξ}) β©) β©
                 {-  β¦ Ξ β§-LK β' β¦ πβ β' (πβ β' Ξ) β§-LCJ               -} _ βΆ'β¨ id' βββ' β¨ β¦ββ§ {Ξ = πβ} {Ξ = πβ β' Ξ} β© β©
                 {-  β¦ Ξ β§-LK β' (β¦ πβ β§-LCJ β' β¦ πβ β' Ξ β§-LCJ)       -} _ βΆ'β¨ β¨ assoc-l-β {{oMonoid}} β»ΒΉ β© β©
                 {-  β¦ Ξ β§-LK β' β¦ πβ β§-LCJ β' β¦ πβ β' Ξ β§-LCJ         -} _ βΆ'β¨ id' βββ' β¨ ββ¦β§β (unit-r-β {a = πβ} β»ΒΉ) β© βββ' id' β©
                 {-  β¦ Ξ β§-LK β' β¦ πβ β' [] β§-LCJ β' β¦ πβ β' Ξ β§-LCJ   -} _ βΆ'β¨ v' βββ' id' β©
                 {-  β¦ Ξ β§-LK β' β¦ [] β’ ββ Ξ±' β§-CJ β' β¦ πβ β' Ξ β§-LCJ  -} _ βΆ'β¨ id' βββ' β¨ unit-l-β {{oMonoid}} β© βββ' id' β©
                 {-  β¦ Ξ β§-LK β' β¦ (ββ Ξ±') β' β¦ πβ β' Ξ β§-LCJ          -} _ βΆ'β¨ varTake {{pβ³}} {Ξ = Ξ} βββ' id' β©
                 {-  β¦ Ξ±' β· Ξ β§-LK β' β¦ πβ β' Ξ β§-LCJ                  -} _ βΆ'β¨ x' β©
                 {-  β¦ Ξ±' β· Ξ β§-LK β' β¦ Ξ±s' β’ Ξ² β§-CJ                   -} _  βΆ'β¨ braid {{pβ³}} βββ' id' β©
                 {-  β¦ Ξ β§-LK β' β¦ Ξ±' β' β¦ Ξ±s' β’ Ξ² β§-CJ                -} _ βΆ'β¨ β¨ assoc-l-β {{oMonoid}} β© β©
                 {-  β¦ Ξ β§-LK β' (β¦ Ξ±' β' β¦ Ξ±s' β’ Ξ² β§-CJ)              -} _ βΆ'β¨ id' βββ' β¨ assoc-l-β {{oMonoid}} β»ΒΉ β© β©
                   β¦ Ξ β§-LK β' β¦ (Ξ±' β· Ξ±s') β’ Ξ² β§-CJ                  βΆid'
          in P

        map-fβ (var {Ξ} {Ξ±} x) =
          let x' = varProj x
          in β¦ Ξ β§-LK β' β               βΆ'β¨ β¨ unit-r-β {{oMonoid}} β© β©
             {- β¦ Ξ β§-LK      -} _              βΆ'β¨ x' β©
             {- β¦ Ξ β’ Ξ± β§-CJ  -} _                βΆ'β¨ id' βββ' β¨ unit-l-β {{oMonoid}} β»ΒΉ β© β©
             β¦ Ξ β§-LK β' β¦ [] β’ Ξ± β§-CJ      βΆid'

      map-f : β{a b} ->
              Subs (MTCDefinitions._β©αΆ '_ Ξ³) β¨ a β© β¨ b β©
              -> Hom (f a) (f b)
      map-f {incl .β¦β¦} {incl .β¦β¦} [] = id'
      map-f {incl .(Ξ β Ξ')} {incl (k β· Ξ)} (_β·_ {Ξ} {Ξ'} x s) =
        let x' = map-fβ x
            s' = map-f s
        in β¦ Ξ β Ξ' β§-LCJ               βΆ'β¨ β¨ β¦ββ§ {Ξ = Ξ} {Ξ = Ξ'} β© β©
           {- β¦ Ξ β§-LCJ β' β¦ Ξ' β§-LCJ       -} _     βΆ'β¨ β¨ unit-l-β {{oMonoid}} β»ΒΉ β© βββ' s' β©
           {- β β' β¦ Ξ β§-LCJ β' β¦ Ξ β§-LCJ   -} _     βΆ'β¨ id' βββ' β¨(ββ¦β§β {Ξ = Ξ} {Ξ' = Ξ β β¦β¦} (unit-r-β β»ΒΉ))β© βββ' id' β©
           {- β β' β¦ Ξ β β¦β¦ β§ β' β¦ Ξ β§-LCJ  -} _ βΆ'β¨ (x' β β¨ unit-l-β {{oMonoid}} β©) βββ' id' β©
           β¦ k β§-CJ β' β¦ Ξ β§-LCJ           βΆid'

      isFunctor:f : isFunctor β² β¨ F Ξ³ β© β² β² β³ β² f
      isFunctor.map isFunctor:f = map-f
      isFunctor.isSetoidHom:map isFunctor:f = {!!}
      isFunctor.functoriality-id isFunctor:f = {!!}
      isFunctor.functoriality-β isFunctor:f = {!!}

    Proof : Functor β² β¨ (F Ξ³) β© β² β² β³ β²
    Proof = f since isFunctor:f

module MTC-Ξ»β2 {π : π} {K : Kinding π} {Ξ³ : MetaTermCalculus K π}
        (β³ : CwJ K π)
        (Ο : Hom-MTC Ξ³ (U β³)) where
  Proof = MTC-Ξ»β.Proof {Ξ³ = Ξ³} {β³ = β¨ β³ β©} Ο

module _ {K : Kinding πβ} where
  instance
    isLogicalFramework:MTC : isLogicalFramework (CwJ K (_ , _ , _)) (MTC K πβ) -- (MTC (π , (π β π)))
    isLogicalFramework.LFTerm (isLogicalFramework:MTC) = F
    isLogicalFramework.LFSig isLogicalFramework:MTC = U
    isLogicalFramework.isFunctor:LFTerm isLogicalFramework:MTC = {!!}
    isLogicalFramework.isFunctor:LFSig isLogicalFramework:MTC = {!!}
    isLogicalFramework.interp isLogicalFramework:MTC {Ξ³} {β³} = MTC-Ξ»β.Proof {Ξ³ = Ξ³} {β³ = β¨ β³ β©}

    -- where
    --   f : β¨ F Ξ³ β© -> β¨ β³ β©
    --   f (incl x) = rec-Ctx-β¦Ώ JObj x -- (Ξ» π§ -> JObj (map-Jdg-β¦Ώ β¨ Ο β© π§)) x
    {-

      open MTCDefinitions Ξ³

      mutual
        -- map-fβ-var : β{a b} ->
        --         (_β©αΆ β_)
        --         -- (map-Ctx-β¦Ώ (Ξ» π§ -> map-Jdg-β¦Ώ kind π§ β main) β¨ a β©)
        --         (map-Ctx-β¦Ώ (map-Jdg-β¦Ώ kind) β¨ a β©)
        --         ((map-Jdg-β¦Ώ kind) b β var) β
        --         Hom (f a) (f (incl ([] ,, b)))

        map-fβ-var : β{a b Ο Ξ± Ξ€} ->
                (_β©αΆ β_)
                (map-Ctx-β¦Ώ (map-Jdg-β¦Ώ kind) β¨ a β©)
                ((map-Ctx-β¦Ώ kind) b β’ Ξ± β var) β
                (β¦ Ξ€ β© Ο β§-R β£ Ξ±) ->
                Hom (f a) (f (incl ([] ,, b β· Ο)))

        map-fβ-var {a} {[]} (getapp ())
        map-fβ-var {a} {(G ,, x)} (MTCDefinitions.getapp ())
        map-fβ-var {a} {(G ,, x)} {[] β’ Ο} {Ξ±} {Ξ€} (suc te te2) p =
          let y1 = map-fβ {Ο = [] β’ ββ x} te refl-β£
              y2 = map-fβ-var {Ο = [] β’ Ο} {Ξ€ = Ξ€} te2 p
          in diag β (map-β (y1 β unit-l-β) (y2 β unit-l-β) β varSkip β unit-l-β-β»ΒΉ)
        map-fβ-var {a} {(G ,, x)} {Ο β’ Ο'} {Ξ±} {Ξ€} (suc te te2) p = {!!}
        map-fβ-var {a} {(G ,, x)} {Ο} {Ξ±} {Ξ€} (zero te) p with arrify-R-kind {Ξ = Ξ€} {Ο = Ο} p
        ... | refl-β£ , refl-β£ =
          let y1 = map-fβ {Ο = [] β’ ββ x} te refl-β£
          in y1 β map-β id (varTake {Ξ = G} {a = x})


        map-fβ-app : β{a b Ο Ξ± Ξ€} ->
                (_β©αΆ β-app_)
                (map-Ctx-β¦Ώ (map-Jdg-β¦Ώ kind) β¨ a β©)
                -- (map-Ctx-β¦Ώ (Ξ» π§ -> map-Jdg-β¦Ώ kind π§ β main) β¨ a β©)
                ((map-Ctx-β¦Ώ kind) b β’ Ξ± β main) β
                (β¦ Ξ€ β© Ο β§-R β£ Ξ±) ->
                Hom (f a) (f (incl ([] ,, b β· Ο)))
        map-fβ-app {a} {b} {G β’ t} {Ξ±} {Ξ€} (MTCDefinitions.app {_} {Ξ±β} {π§} q x y) p =
          let t1 = map-fβ-app {_} {_} {(G) β’ t} {_} {Ξ€ = ([] ,, π§) β Ξ€} x {!!}
              t2 = map-fβ {_} {_} {π§} y q
              -- t2 = map-fβ {_} {_} {[] β’ Ξ±β} y refl-β£
          in {!!}
        map-fβ-app {a} {b} {Ο} {Ξ±} {Ξ€} (var x) p = map-fβ-var {a} {b} {Ο} {Ξ±} {Ξ€} x p
        map-fβ-app {a} {b} (con {_} {ts β© t} x xβ) p = {!!}
        map-fβ-app {a} {b} (meta x) p = {!!}

        -- assign-r : Ctx-β¦Ώ K

        map-fβ : β{a b Ο Ξ±} ->
                (_β©αΆ β_)
                (map-Ctx-β¦Ώ (map-Jdg-β¦Ώ kind) β¨ a β©)
                -- ((map-Jdg-β¦Ώ kind) b β main) β
                ((map-Ctx-β¦Ώ kind) b β’ Ξ± β main) β
                (β¦ Ο β§-J β£ Ξ±) ->
                Hom (f a) (f (incl ([] ,, b β· Ο)))
        map-fβ {a} {b} {G β’ t} {(Ξ± β Ξ²)} (MTCDefinitions.lam x) p with arrify-J-split {G} p
        ... | Ξ' , Ξ±' , (refl-β£ , refl-β£) , r = let y = map-fβ {Ο = Ξ' β’ t} x r
                                                in y β {!!}
        map-fβ {a} {b} {G β’ t} {.(kind _)} (MTCDefinitions.getapp x) p with arrify-J-kind {G} p
        ... | (refl-β£ , refl-β£) = map-fβ-app {Ξ€ = []} x p


        -- map-fβ {a} {b} (getapp x) = map-fβ-app x
      -- map-fβ {a} {([] β’ Ξ±)} (getapp x) = {!!}
      -- map-fβ {a} {((Ξ ,, Ξ²) β’ Ξ±)} (getapp x) = {!!}
      -- map-fβ {a} {((Ξ ,, Ξ²) β’ Ξ±) β var} (t) = map-fβ-var t
      -- map-fβ {a} {((Ξ ,, Ξ²) β’ .Ξ²) β .var} (zero (getapp (meta x))) = {!!}

      map-f : β{a b} ->
              Sub-β¦Ώ (MTCDefinitions._β©αΆ β'_ Ξ³)
              -- (map-Ctx-β¦Ώ (Ξ» π§ -> map-Jdg-β¦Ώ kind π§ β main) β¨ a β©)
              -- (map-Ctx-β¦Ώ (Ξ» π§ -> map-Jdg-β¦Ώ kind π§ β main) β¨ b β©) ->
              (map-Ctx-β¦Ώ (map-Jdg-β¦Ώ kind) β¨ a β©)
              (map-Ctx-β¦Ώ (map-Jdg-β¦Ώ kind) β¨ b β©) β
              Hom (f a) (f b)
      map-f = {!!}

      isFunctor:f : isFunctor β² β¨ F Ξ³ β© β² β² β¨ β³ β© β² f
      isFunctor.map isFunctor:f = map-f
      isFunctor.isSetoidHom:map isFunctor:f = {!!}
      isFunctor.functoriality-id isFunctor:f = {!!}
      isFunctor.functoriality-β isFunctor:f = {!!}
      -}



{-
{-

-- instance
--   isCategory:MetaTermCalculus : isCategory (ββ , ββ) (MetaTermCalculus)
--   isCategory.Hom' isCategory:MetaTermCalculus = {!!}
--   isCategory.isSetoid:Hom isCategory:MetaTermCalculus = {!!}
--   isCategory.id isCategory:MetaTermCalculus = {!!}
--   isCategory._β_ isCategory:MetaTermCalculus = {!!}
--   isCategory.unit-l-β isCategory:MetaTermCalculus = {!!}
--   isCategory.unit-r-β isCategory:MetaTermCalculus = {!!}
--   isCategory.unit-2-β isCategory:MetaTermCalculus = {!!}
--   isCategory.assoc-l-β isCategory:MetaTermCalculus = {!!}
--   isCategory.assoc-r-β isCategory:MetaTermCalculus = {!!}
--   isCategory._β_ isCategory:MetaTermCalculus = {!!}

-- macro
--   πππ = #structureOn MetaTermCalculus


-- instance
--   isLogicalFramework:MetaTermCalculus : isLogicalFramework (ππ¨π§πππ­ _) πππ
--   isLogicalFramework.Term isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.Sig isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.isFunctor:Term isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.isFunctor:Sig isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.β¦ isLogicalFramework:MetaTermCalculus β§ = {!!}


-}
-}
