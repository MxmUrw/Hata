
module Verification.Old.Core.Category.Functor.Representable where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Proper
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Functor.Presheaf
open import Verification.Old.Core.Category.Instance.Set
open import Verification.Old.Core.Category.Iso
open import Verification.Old.Core.Homotopy.Level


-- like in https://github.com/agda/agda-categories/blob/master/src/Categories/Functor/Hom.agda

-- record ISetoid (A : ๐ฐ ๐) ๐ : ๐ฐ (๐ ๏ฝค ๐ โบ) where
--   field {{ISet:this}} : ISet A
--         _โผ_ : A -> A -> ๐ฐ ๐
--         {{IEquiv:โผ}} : IEquiv _โผ_
-- unquoteDecl Setoid setoid

-- ===* Representable functors
-- | For this concept, we first need to define the hom-functors.

-- [Definition]
-- | Let [..] be a category which is a "proper" 1-category [..].
module _ {๐ : Category ๐} {{๐P : I1Category ๐}} where

-- | - The covariant hom-functor is given for any |a : ๐|:
  Functor:Hom : โ(a : โจ ๐ โฉ) -> Functor ๐ ` Set (๐ โ 1) `
  (โจ Functor:Hom a โฉ) b = ` Hom a b `
  โจ IFunctor.map (of Functor:Hom a) f โฉ g = g โ f
  IFunctor.functoriality-id (of Functor:Hom a) x = โฃโโก unit-r-โ
  IFunctor.functoriality-โ (of Functor:Hom a) x = โฃโโก assoc-r-โ
  IFunctor.functoriality-โฃ (of Functor:Hom a) p f = โฃโโก (refl โ p)

-- | - The contravariant hom-functor is given for any |b : ๐|:
  Functor:Homแตแต : โ(b : โจ ๐ โฉ) -> Functor (๐ แตแต) ` Set (๐ โ 1)`
  (โจ Functor:Homแตแต b โฉ) a = ` Hom a b `
  โจ IFunctor.map (of Functor:Homแตแต b) g โฉ f = g โ f
  IFunctor.functoriality-id (of Functor:Homแตแต b) _ = โฃโโก unit-l-โ
  IFunctor.functoriality-โ (of Functor:Homแตแต b) _ = โฃโโก assoc-l-โ
  IFunctor.functoriality-โฃ (of Functor:Homแตแต b) p g = โฃโโก (p โ refl)
-- //

-- [Definition]
-- | - We say that a covariant functor |F : ๐ แตแต โถ Set| is corepresented by an object |x : ๐|, if:
  record .Old.Core.resentation (F : PSh (๐ แตแต) (๐ โ 1)) (x : โจ ๐ โฉ) : ๐ฐ ๐ where
    field corep : Functor:Hom x โ F

  open .Old.Core.resentation public

-- | - Likewise, we say that a contravariant functor |F : ๐ โถ Set| is represented by an object |x : ๐|, if:
  record IRepresentation (F : PSh ๐ (๐ โ 1)) (x : โจ ๐ โฉ) : ๐ฐ ๐ where
    field rep : Functor:Homแตแต x โ F
  open IRepresentation public
-- //

unquoteDecl Representation representation = #struct "Rep" (quote IRepresentation) "x" Representation representation
unquoteDecl.Old.Core.resentation corepresentation = #struct .Old.Core." (quote .Old.Core.resentation) "x".Old.Core.resentation corepresentation



