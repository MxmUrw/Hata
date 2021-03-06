
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.SuccessFlexFlex where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Set.Function.Injective

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Adjunction
open import Verification.Core.Data.NormalFiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Renaming.Instance.hasEqualizers

open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Functor.RelativeAdjoint
open import Verification.Core.Category.Std.Limit.Specific.Equalizer.Definition

open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition


-- here i need to show that when i have (meta Mx tsx) (meta My tsy) then


module _ {K : Kinding ????} {{_ : isMetaTermCalculus ???? K}} where


  reset-with-meta : ???{???? : ???List (Jdg??? ??? K ???)} {?? ?? : ??? InjVars ???} {?? : ??? K ???}
                  -- -> (M : ???? ??? ((??? ??? ?? ??? ??? ??? ??))) ->
                  -> (s : ?? ??? ??)
                  -> ???? ??????-pat (??? ??? ?? ??? ??? ??? ??) -> ???? ??????-pat (??? ??? ?? ??? ??? ??? ??)
  reset-with-meta {????} {??} {??} ?? (app-meta M s) = app-meta M {!!}
  reset-with-meta {????} {??} {??} ?? (app-var x x???) = {!!}
  reset-with-meta {????} {??} {??} ?? (app-con x x???) = {!!}

  unify-meta-meta-same : ???{???? : ???List (Jdg??? ??? K ???)} {?? ?? : ??? InjVars ???} {?? : ??? K ???}
                  -> (M : ???? ??? ((??? ??? ?? ??? ??? ??? ??))) -> (s t : ?? ??? ??) -> ???? ??????-pat (??? ??? ?? ??? ??? ??? ??)
  unify-meta-meta-same M s t = app-meta {?? = Eq {{hasEqualizers:???????????????}} s t} {!!} {!!}






