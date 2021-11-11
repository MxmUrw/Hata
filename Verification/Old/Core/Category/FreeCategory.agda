
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.FreeCategory where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.Functor.Adjunction
open import Verification.Old.Core.Category.Iso
open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Algebra.Basic.Monoid
-- open import Verification.Old.Core.Order.Lattice
-- open import Verification.Old.Core.Order.Instance.Level
-- open import Verification.Old.Core.Order.Instance.Product


-- a #Notation/Rewrite# QPathStr = Path^Q

-- Let [..] be a set with a quiver structure [..].
-- [Hide]
module _ {Q : 𝒰 𝑖} {{IQuiver:Q : IQuiver Q 𝑗}} where

  data QPath : Q -> Q -> 𝒰 (𝑖 ､ 𝑗) where
    last : ∀ {a b} -> Edge a b -> QPath a b
    _∷_ : ∀{a b c : Q} -> Edge a b -> QPath b c -> QPath a c

  comp-QPath : ∀{a b c : Q} -> QPath a b -> QPath b c -> QPath a c
  comp-QPath (last x) f = x ∷ f
  comp-QPath (x ∷ e) f = x ∷ comp-QPath e f

  data QPathOn : (List Q) -> Q -> 𝒰 (𝑖 ､ 𝑗) where
    last : ∀ {a b} -> Edge a b -> QPathOn (a ∷ []) b
    _∷_ : ∀{a b c : Q} {bs : List Q} -> Edge a b -> QPathOn (b ∷ bs) c -> QPathOn (a ∷ b ∷ bs) c


  data _∼-On_ : {L : List Q} {c : Q} -> QPathOn L c -> QPathOn L c -> 𝒰 (𝑖 ､ 𝑗) where
    last : ∀{a b : Q} -> {e f : Edge a b} -> (e ≈ f) -> last e ∼-On last f
    _∷_ : ∀{a b c : Q} {bs : List Q} -> {e f : Edge a b} -> (e ≈ f) -> {p q : QPathOn (b ∷ bs) c} -> p ∼-On q -> _∷_ e p ∼-On _∷_ f q

  comp-QPathOn : ∀{b c : Q} -> ∀{as bs : List Q} -> QPathOn as b -> QPathOn (b ∷ bs) c -> QPathOn (as ⋅ (b ∷ bs)) c
  comp-QPathOn (last x) q = x ∷ q
  comp-QPathOn (x ∷ p) q = x ∷ (comp-QPathOn p q)


  record QPathStr (a b : Q) : 𝒰 (𝑖 ､ 𝑗) where
    constructor _,_
    field nodes : List Q
          path : QPathOn (a ∷ nodes) b

  open QPathStr

  comp-QPathStr : ∀{a b c : Q} -> QPathStr a b -> QPathStr b c -> QPathStr a c
  comp-QPathStr {a = a} {b} {c} (ps , p) (qs , q) = (ps ⋅ (b ∷ qs)) , comp-QPathOn p q

  ϕ : ∀{a b : Q} -> QPathStr a b -> QPath a b
  ϕ ([] , last x) = last x
  ϕ ((x ∷ ps) , (y ∷ p)) = y ∷ ϕ (ps , p)

  ψ : ∀{a b : Q} -> QPath a b -> QPathStr a b
  ψ (last x) = [] , last x
  ψ (x ∷ e) = let (e1 , e2) = ψ e
              in (_ ∷ e1 , x ∷ e2)

  ψϕ⟲ : ∀{a b : Q} -> ∀ (e : QPath a b) -> ϕ (ψ e) ≡ e
  ψϕ⟲ (last x) = refl
  ψϕ⟲ (x ∷ e) = λ i -> x ∷ ψϕ⟲ e i

  ψϕ⟳ : ∀{a b : Q} -> ∀ (e : QPathStr a b) -> ψ (ϕ e) ≡ e
  ψϕ⟳ (.[] , last x) = refl
  ψϕ⟳ ((_ ∷ es) , (x ∷ e)) =
    let P = ψϕ⟳ (es , e)
    in λ i -> (_ ∷ P i .nodes , x ∷ P i .path)

  strictify : ∀{a b : Q} -> QPath a b ≅-𝒰 QPathStr a b
  ⟨ strictify ⟩ = ψ
  IIso-𝒰.inverse-𝒰 (of strictify) = ϕ
  IIso-𝒰./⟲-𝒰 (of strictify) = funExt ψϕ⟲
  IIso-𝒰./⟳-𝒰 (of strictify) = funExt ψϕ⟳

  switch::ψ,comp2 : ∀{a b c : Q} -> (e : QPath a b) -> (f : QPath b c) -> ϕ (ψ (comp-QPath e f)) ≡ ϕ (comp-QPathStr (ψ e) (ψ f))
  switch::ψ,comp2 (last x) f = refl
  switch::ψ,comp2 (x ∷ e) f = λ i -> x ∷ switch::ψ,comp2 e f i

  switch::ψ,comp : ∀{a b c : Q} -> (e : QPath a b) -> (f : QPath b c) -> ψ (comp-QPath e f) ≡ comp-QPathStr (ψ e) (ψ f)
  switch::ψ,comp e f = sym (ψϕ⟳ _) ∙ cong ψ (switch::ψ,comp2 e f) ∙ ψϕ⟳ _


  module _ (a b : Q) where
    ∼-over : {xs ys : List Q} -> (Id xs ys) -> (p : QPathOn (a ∷ xs) b) (q : QPathOn (a ∷ ys) b) -> 𝒰 _
    ∼-over r p q = transport-Id (λ ξ -> QPathOn (a ∷ ξ) b) r p ∼-On q

  record _∼_ {a b : Q} (p q : QPathStr a b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor _,_
    field nodes≡ : Id (nodes p) (nodes q)
          path≡ : ∼-over a b nodes≡ (path p) (path q)

  compat-QPathOn : ∀{a b c : Q} -> ∀{as bs : List Q} {e f : QPathOn (a ∷ as) b} {g h : QPathOn (b ∷ bs) c}
                   -> e ∼-On f -> g ∼-On h -> (comp-QPathOn e g) ∼-On (comp-QPathOn f h)
  compat-QPathOn (last x) q = x ∷ q
  compat-QPathOn (x ∷ p) q = x ∷ compat-QPathOn p q

  compat-QPathStr-helper : ∀{a b c : Q} {(es , e) : QPathStr a b} {(gs , g) : QPathStr b c}
                          -> ∀Id (λ fs (ps : Id es fs) -> ∀ f
                          -> ∀Id (λ hs (qs : Id gs hs) -> ∀ h
                          -> ∼-over a b ps e f -> ∼-over b c qs g h -> ∼-over a c (cong₂-Id (λ xs ys -> xs ⋅ (b ∷ ys)) ps qs) (comp-QPathOn e g) (comp-QPathOn f h)))
  compat-QPathStr-helper {a = a} {b} {c} {es , e} {gs , g} = J-∀Id (λ f -> J-∀Id (λ h -> compat-QPathOn))

-- (p : e ∼ f) -> (q : g ∼ h) -> (comp-QPathStr e g ∼ comp-QPathStr f h)

  compat-QPathStr : ∀{a b c : Q} {e f : QPathStr a b} {g h : QPathStr b c} -> (p : e ∼ f) -> (q : g ∼ h) -> (comp-QPathStr e g ∼ comp-QPathStr f h)
  compat-QPathStr {a} {b} {c} {e = es , e} (ps , p) (qs , q) =
    (cong₂-Id (λ xs ys -> xs ⋅ (b ∷ ys)) ps qs) , compat-QPathStr-helper {a} {b} {c} {es , e} .getProof ps _ .getProof qs _ p q

  -- _∼_ {a} {b} (l , p) (m , q) = ∑ λ (l≡m : Id l m) -> ∼-over a b l≡m p q

  refl-∼-On : ∀{a b : Q} -> {xs : List Q} -> (p : QPathOn (a ∷ xs) b ) -> p ∼-On p
  refl-∼-On (last x) = last refl
  refl-∼-On (x ∷ p) = refl ∷ refl-∼-On p

  sym-∼-On : ∀{a b : Q} -> {xs : List Q} -> {p q : QPathOn (a ∷ xs) b} -> p ∼-On q -> q ∼-On p
  sym-∼-On (last x) = last (sym x)
  sym-∼-On (x ∷ r) = sym x ∷ sym-∼-On r

  trans-∼-On : ∀{a b : Q} -> {xs : List Q} -> {o p q : QPathOn (a ∷ xs) b} -> o ∼-On p -> p ∼-On q -> o ∼-On q
  trans-∼-On (last r) (last s) = last (r ∙ s)
  trans-∼-On (e ∷ r) (f ∷ s) = (e ∙ f) ∷ (trans-∼-On r s)


  refl-∼ : ∀{a b : Q} -> {p : QPathStr a b} -> p ∼ p
  refl-∼ {a} {b} {xs , p} = refl , refl-∼-On _


  sym-∼-helper : ∀{a b : Q} -> ∀{xs : List Q} -> ∀Id (λ ys (r1 : Id xs ys) -> ∀ {p q} -> (∼-over a b r1 p q) -> (∼-over a b (sym-Id r1) q p))
  sym-∼-helper {a} {b} {xs} = J-∀Id (sym-∼-On)

  sym-∼ : ∀{a b : Q} -> ∀{p q : QPathStr a b} -> (p ∼ q) -> (q ∼ p)
  sym-∼ (r1 , r2) = (sym r1) , sym-∼-helper .getProof r1 r2

  trans-∼-helper : ∀{a b} -> ∀{xs : List Q} -> ∀Id (λ ys (r1 : Id xs ys) -> ∀Id (λ zs (r2 : Id ys zs) -> ∀ o p q -> (∼-over a b r1 o p) -> ∼-over a b r2 p q -> ∼-over a b (r1 ∙ r2) o q))
  trans-∼-helper {a} {b} {xs} = J-∀Id (J-∀Id (λ _ _ _ -> trans-∼-On))

  trans-∼ : ∀{a b} -> {f g h : QPathStr a b} -> (p : f ∼ g) -> (q : g ∼ h) -> f ∼ h
  trans-∼ {f = fs , f} {g = gs , g} {h = hs , h} (ps , p) (qs , q) = ps ∙ qs , trans-∼-helper .getProof ps .getProof qs f g h p q


  -- module _ where
  --   private
  --     infixl 50 _⋆_
  --     _⋆_ = comp-QPathStr

  --   assoc-l-◆-QPathStr : ∀{a b c d : Q} -> (e : QPathStr a b) -> (f : QPathStr b c) -> (g : QPathStr c d) -> (e ⋆ f) ⋆ g ∼ e ⋆ (f ⋆ g)
  --   assoc-l-◆-QPathStr e f g = {!!} , {!!}

  instance
    isEquivRel:∼ : ∀{a b : Q} -> isEquivRel (λ (p q : QPathStr a b) -> p ∼ q)
    isEquivRel.refl isEquivRel:∼ = refl-∼
    isEquivRel.sym isEquivRel:∼ = sym-∼
    isEquivRel._∙_ isEquivRel:∼ = trans-∼

  data QPath₊ : (a b : Q) -> 𝒰 (𝑖 ､ 𝑗) where
    id-Q : ∀{a : Q} -> QPath₊ a a
    some : ∀{a b : Q} -> QPath a b -> QPath₊ a b

  data _∼₂_ : {a b : Q} (e f : QPath₊ a b) -> 𝒰 (𝑖 ､ 𝑗) where
    id-Q : ∀{a} -> id-Q {a} ∼₂ id-Q {a}
    some : ∀{a b : Q} -> {e f : QPath a b} -> ψ e ∼ ψ f -> some (e) ∼₂ some (f)

  refl-∼₂ : ∀{a b : Q} -> (e : QPath₊ a b) -> e ∼₂ e
  refl-∼₂ id-Q = id-Q
  refl-∼₂ (some x) = some refl

  sym-∼₂ : ∀{a b : Q} -> {e f : QPath₊ a b} -> e ∼₂ f -> f ∼₂ e
  sym-∼₂ id-Q = id-Q
  sym-∼₂ (some x) = some (sym x)

  trans-∼₂ : ∀{a b : Q} -> {e f g : QPath₊ a b} -> e ∼₂ f -> f ∼₂ g -> e ∼₂ g
  trans-∼₂ id-Q id-Q = id-Q
  trans-∼₂ (some p) (some q) = some (p ∙ q)

  instance
    isEquivRel:∼₂ : ∀{a b : Q} -> isEquivRel (λ (p q : QPath₊ a b) -> p ∼₂ q)
    isEquivRel.refl isEquivRel:∼₂ = refl-∼₂ _
    isEquivRel.sym isEquivRel:∼₂ = sym-∼₂
    isEquivRel._∙_ isEquivRel:∼₂ = trans-∼₂

  module _ where
    private
      infixl 50 _⋆_
      _⋆_ = comp-QPath

    assoc-l-◆-QPath : ∀{a b c d : Q} -> (e : QPath a b) -> (f : QPath b c) -> (g : QPath c d) -> ((e ⋆ f) ⋆ g) ≡ (e ⋆ (f ⋆ g))
    assoc-l-◆-QPath (last x) f g = refl
    assoc-l-◆-QPath (x ∷ e) f g = λ i -> x ∷ assoc-l-◆-QPath e f g i

    assoc-l-◆-QPath2 : ∀{a b c d : Q} -> (e : QPath a b) -> (f : QPath b c) -> (g : QPath c d) -> ψ ((e ⋆ f) ⋆ g) ∼ ψ (e ⋆ (f ⋆ g))
    assoc-l-◆-QPath2 e f g = transport (λ i -> ψ (e ⋆ f ⋆ g) ∼ ψ (assoc-l-◆-QPath e f g i)) refl

  comp-QPath₊ : ∀{a b c : Q} -> QPath₊ a b -> QPath₊ b c -> QPath₊ a c
  comp-QPath₊ id-Q g = g
  comp-QPath₊ (some f) id-Q = some f
  comp-QPath₊ (some f) (some g) = some (comp-QPath f g)

  private
    infixl 50 _*_
    _*_ = comp-QPath₊

  unit-r-◆-QPath₊ :  ∀{a b : Q} -> (e : QPath₊ a b) -> e * id-Q ∼₂ e
  unit-r-◆-QPath₊ id-Q = refl
  unit-r-◆-QPath₊ (some x) = refl

  assoc-l-◆-QPath₊ : ∀{a b c d : Q} -> (e : QPath₊ a b) -> (f : QPath₊ b c) -> (g : QPath₊ c d) -> (e * f) * g ∼₂ e * (f * g)
  assoc-l-◆-QPath₊ id-Q f g = refl
  assoc-l-◆-QPath₊ (some x) id-Q g = refl
  assoc-l-◆-QPath₊ (some x) (some x₁) id-Q = refl
  assoc-l-◆-QPath₊ (some e) (some f) (some g) = some (assoc-l-◆-QPath2 e f g)

  compat-QPath₊ : ∀{a b c} -> {e f : QPath₊ a b} {g h : QPath₊ b c} -> (p : e ∼₂ f) (q : g ∼₂ h) -> (e * g ∼₂ f * h)
  compat-QPath₊ id-Q q = q
  compat-QPath₊ (some x) id-Q = some x
  compat-QPath₊ {e = some e} {some f} {some g} {some h} (some p) (some q) =
    let P = compat-QPathStr p q
    in some (transport (λ i -> switch::ψ,comp e g (~ i) ∼ switch::ψ,comp f h (~ i)) P)


Category:Free : Quiver 𝑖 -> Category (𝑖 ⌄ 0 , ⩚ 𝑖 , ⩚ 𝑖)
⟨ Category:Free Q ⟩ = ⟨ Q ⟩
isCategory.Hom (of Category:Free Q) = QPath₊
isCategory._≣_ (of Category:Free Q) = _∼₂_
isCategory.isEquivRel:≣ (of Category:Free Q) = isEquivRel:∼₂
isCategory.id (of Category:Free Q) = id-Q
isCategory._◆_ (of Category:Free Q) = comp-QPath₊
isCategory.unit-l-◆ (of Category:Free Q) = refl
isCategory.unit-r-◆ (of Category:Free Q) = unit-r-◆-QPath₊ _
isCategory.unit-2-◆ (of Category:Free Q) = refl
isCategory.assoc-l-◆ (of Category:Free Q) {f = f} {g} {h} = assoc-l-◆-QPath₊ f g h
isCategory.assoc-r-◆ (of Category:Free Q) {f = f} {g} {h} = sym (assoc-l-◆-QPath₊ f g h)
isCategory._◈_ (of Category:Free Q) = compat-QPath₊
-- //

-- Here we begin to build the adjunction.
-- [Hide]
private
  module _ {C : 𝒰 𝑖} {{_ : isCategory C 𝑗}} where
    Qvr = (Category:Forget (category C))
    instance _ = of Qvr

    map-eval-impl : ∀{a b : C} -> QPath a b -> Hom a b
    map-eval-impl (last e) = e
    map-eval-impl (e ∷ es) = e ◆ map-eval-impl es

    map-eval : ∀{a b : C} -> QPath₊ a b -> Hom a b
    map-eval id-Q = id
    map-eval (some e) = map-eval-impl e

    map-eval-impl::functoriality : ∀{a b c : C} -> (e : QPath a b) (f : QPath b c) -> map-eval-impl (comp-QPath e f) ≣ map-eval-impl e ◆ map-eval-impl f
    map-eval-impl::functoriality (last x) f = refl
    map-eval-impl::functoriality (x ∷ e) f = (refl ◈ P) ∙ (assoc-r-◆)
      where P = map-eval-impl::functoriality e f

    map-eval::functoriality : ∀{a b c : C} -> (e : QPath₊ a b) (f : QPath₊ b c) -> map-eval (comp-QPath₊ e f) ≣ map-eval e ◆ map-eval f
    map-eval::functoriality id-Q e = sym unit-l-◆
    map-eval::functoriality (some e) id-Q = sym unit-r-◆
    map-eval::functoriality (some e) (some f) = map-eval-impl::functoriality e f

eval-Category:Free : ∀{𝒞 : Category 𝑖} -> Functor (Category:Free (Category:Forget 𝒞)) 𝒞
⟨ eval-Category:Free ⟩ a = a
IFunctor.map (of eval-Category:Free) = map-eval
IFunctor.functoriality-id (of eval-Category:Free) = refl
IFunctor.functoriality-◆ (of eval-Category:Free) {f = f} {g = g} = map-eval::functoriality f g
IFunctor.functoriality-≣ (of eval-Category:Free) = {!!}


module _ {Q : Quiver 𝑖} {R : Quiver 𝑗} (F : QuiverHom Q R) where
  private
    QCat = Category:Free Q
    RCat = Category:Free R
    instance _ = of QCat
    instance _ = of RCat

    map-F-impl : {a b : ⟨ Q ⟩} (e : QPath a b) -> QPath (⟨ F ⟩ a) (⟨ F ⟩ b)
    map-F-impl (last x) = last (qmap x)
    map-F-impl (e ∷ es) = qmap e ∷ map-F-impl es

    map-F : {a b : ⟨ Q ⟩} (e : QPath₊ a b) -> QPath₊ (⟨ F ⟩ a) (⟨ F ⟩ b)
    map-F id-Q = id-Q
    map-F (some e) = some (map-F-impl e)

    functoriality-◆/map-F-impl : {a b c : ⟨ Q ⟩} (e : QPath a b) (f : QPath b c) -> (map-F-impl (comp-QPath e f)) ≡ (comp-QPath (map-F-impl e) (map-F-impl f))
    functoriality-◆/map-F-impl (last x) p = refl
    functoriality-◆/map-F-impl (x ∷ e) f = λ i -> (qmap x) ∷ functoriality-◆/map-F-impl e f i

    functoriality-◆/map-F : {a b c : ⟨ Q ⟩} (e : QPath₊ a b) (f : QPath₊ b c) -> map-F (e ◆ f) ≣ map-F e ◆ map-F f
    functoriality-◆/map-F id-Q f = refl
    functoriality-◆/map-F (some e) id-Q = refl
    functoriality-◆/map-F (some e) (some f) = some (fromPath (cong ψ (functoriality-◆/map-F-impl e f)))

  map-Category:Free : (Functor (Category:Free Q) (Category:Free R))
  ⟨ map-Category:Free ⟩ = ⟨ F ⟩
  IFunctor.map (of map-Category:Free) = map-F
  IFunctor.functoriality-id (of map-Category:Free) = refl
  IFunctor.functoriality-◆ (of map-Category:Free) {f = f} {g} = functoriality-◆/map-F f g
  IFunctor.functoriality-≣ (of map-Category:Free) {f = f} {g} = {!!}
-- //

-- [Lemma]
-- | There is a functor [..]. In fact, it is right adjoint to the forgetful functor |Category:Category ⟶ Category:Quiver|.
Functor:Category:Free : Functor (Category:Quiver 𝑖) (Category:Category _)
-- //
-- [Hide]
⟨ Functor:Category:Free ⟩ = Category:Free
IFunctor.map (of Functor:Category:Free) = map-Category:Free
IFunctor.functoriality-id (of Functor:Category:Free) = {!!}
IFunctor.functoriality-◆ (of Functor:Category:Free) = {!!}
IFunctor.functoriality-≣ (of Functor:Category:Free) = {!!}
-- //

--------------------------------------------------------------------
-- Discrete categories and quivers

-- [Hide]
Quiver:Discrete : (X : 𝒰 𝑖) -> Quiver (𝑖 , 𝑖 , 𝑖)
⟨ Quiver:Discrete X ⟩ = X
IQuiver.Edge (of (Quiver:Discrete X)) _ _ = `𝟘`
IQuiver._≈_ (of (Quiver:Discrete X)) a b = a ≡ b
IQuiver.isEquivRelInst (of (Quiver:Discrete X)) = isEquivRel:Path

instance IQuiver:Discrete = #openstruct Quiver:Discrete

Category:Discrete : (X : 𝒰 𝑖) -> Category (𝑖 , 𝑖 , 𝑖)
Category:Discrete X = Category:Free (Quiver:Discrete X)

instance
  IQuiverHom:FromDiscrete : ∀{X : 𝒰 𝑖} {Q : Quiver 𝑗} -> {f : X -> ⟨ Q ⟩} -> IQuiverHom (Quiver:Discrete X) Q f
  IQuiverHom.qmap IQuiverHom:FromDiscrete (lift ())


instance
  Cast:Edge : ∀{Q : Quiver 𝑖} -> ∀{a b : ⟨ Q ⟩} -> Cast (Edge {{of Q}} a b) IAnything (Hom {{of Category:Free Q}} a b)
  Cast.cast Cast:Edge e = some (last e)

instance
  Cast:QPath : ∀{Q : Quiver 𝑖} -> ∀{a b : ⟨ Q ⟩} -> Cast (QPath {{of Q}} a b) IAnything (Hom {{of Category:Free Q}} a b)
  Cast.cast Cast:QPath e = some e

instance
  Cast:LiftEdge : ∀{𝑗 : 𝔏} -> ∀{Q : Quiver (many ℓ₀)} -> ∀{a b : ⟨ Q ⟩} -> Cast (Edge {{of Q}} a b) IAnything (Lift {j = 𝑗} (Hom {{of Category:Free Q}} (a) (b)))
  Cast.cast Cast:LiftEdge e = ↥ (some (last e))
-- //

--   IFunctor:Category:Free : IFunctor (⌘ Quiver 𝑖) (⌘ Category _) Category:Free
--   IFunctor.map IFunctor:Category:Free = map-Category:Free
--   IFunctor.functoriality-id IFunctor:Category:Free = {!!}
--   IFunctor.functoriality-◆ IFunctor:Category:Free = {!!}

-- Functor:Category:Free : Functor (⌘ Quiver 𝑖) (⌘ Category _)
-- Functor:Category:Free = functor Category:Free


{-
-- [Definition]
-- | A quiver path [...] in |Q| has the following constructors:
  data QPathStr : (a b : Q) -> 𝒰 (𝑖 ､ 𝑗) where

-- | - The identity path [..] on a vertex |a|.
    end : ∀{a : Q} -> QPathStr a a

-- | - A path from |a| to |b|, concatenated with an edge |b| to |c|.
    _∷_ : ∀{a c : Q} -> (b : Q) -> QPathStr a b -> Edge b c -> QPathStr a c
-- //
  pattern _:[_]:_ p b q = _∷_ b p q
-}


{-
  -- | Paths can be composed by:
  comp-QPathStr : ∀{a b c : Q} -> QPathStr a b -> QPathStr b c -> QPathStr a c
  comp-QPathStr f end = f
  comp-QPathStr f (g :[ _ ]: x) = comp-QPathStr f g :[ _ ]: x

  -- |> We can embed edges into paths:
  ι-QPathStr : {a b : Q} (f : Edge a b) -> QPathStr a b
  ι-QPathStr f = end :[ _ ]: f

  withSameVertex : ∀{A : 𝒰 𝑘} -> ∀{a b c d : Q} -> (a ≡ b) -> (c ≡ d) -> (P : Edge a b -> Edge a b -> A) -> Edge a c -> Edge b d -> A
  withSameVertex p q P e f = {!!}


  QPathList : (a b : Q) -> List Q -> 𝒰 _
  QPathList a b [] = Lift ⊤
  QPathList a b (x ∷ []) = Edge a b
  QPathList a b (x ∷ l ∷ ls) = Edge a x ×-𝒰 QPathList x b (l ∷ ls)

  getList : ∀{a b : Q} -> QPathStr a b -> List Q
  getList end = []
  getList (ps :[ b ]: p) = b ∷ getList ps

  Both : (a b : Q) -> 𝒰 _
  Both a b = ∑ λ l -> QPathList a b l

  intoBoth : ∀{a b : Q} -> (p : QPathStr a b) -> QPathList a b (getList p)
  intoBoth end = lift tt
  intoBoth (end :[ b ]: x) = x
  intoBoth ((p :[ b₁ ]: x₁) :[ b ]: x) = {!!} , {!!}
  -- intoBoth end = [] , lift tt
  -- intoBoth (end :[ b ]: x) = (b ∷ []) , x
  -- intoBoth ((p :[ b ]: x) :[ c ]: y) = {!!}


  _∼-On_ : ∀{a b : Q} -> (p q : QPathStr a b) -> 𝒰 (𝑖 ､ 𝑗)
  _∼-On_ p q = p ≡ q

  ∼-On-refl : ∀{a b : Q} -> {p : QPathStr a b} -> p ∼-On p
  ∼-On-refl = {!!}
  -- end ∼-On q = q ≡ end
  -- (p  x) ∼-On end = Lift ⊥
  -- (_,_ {b = b} ps p) ∼-On (_,_ {b = b2} qs q) = Lift {j = 𝑖 ⊔ ¡ 𝑗} $ ∑ λ (s : b ≡ b2) -> withSameVertex s refl (λ p1 p2 -> p1 ≈ p2) p q -- (p ≈ q) -- ×-𝒰 (ps ∼-On qs)

-- instance
-- isCategory:Category:Free : {Q : Quiver 𝑖} -> isCategory ⟨ Q ⟩ (⨆ 𝑖 , ⨆ 𝑖)
-- isCategory.Hom (isCategory:Category:Free {Q = Q} ) = QPathStr Q
-- isCategory._≣_ (isCategory:Category:Free) = {!!}
-- isCategory.isEquivRel:≣ (isCategory:Category:Free) = {!!}
-- isCategory.id (isCategory:Category:Free) = end
-- isCategory._◆_ (isCategory:Category:Free) = comp-QPath
-- isCategory._◈_ (isCategory:Category:Free) = {!!}
-- isCategory.unit-l-◆ isCategory:Category:Free = {!!}
-- isCategory.unit-r-◆ isCategory:Category:Free = {!!}
-- isCategory.unit-2-◆ isCategory:Category:Free = {!!}
-- isCategory.assoc-l-◆ isCategory:Category:Free = {!!}
-- isCategory.assoc-r-◆ isCategory:Category:Free = {!!}
-- category ⟨ Q ⟩ {{isCategory:Category:Free {Q = Q}}}

-- [Definition]
-- | Given any quiver |Q|, the free category on this quiver is constructed
--   by a function [..]. The objects of |Category:Free Q| are the vertices of |Q|,
--   and the morphisms are paths in |Q|.
Category:Free : Quiver 𝑖 -> Category (𝑖 ⌄ 0 , ¡ 𝑖 , ¡ 𝑖)
⟨ Category:Free Q ⟩                 = ⟨ Q ⟩
isCategory.Hom (of Category:Free Q)  = QPath
-- | The rest is as follows:
isCategory._≣_ (of Category:Free Q) = _∼-On_
isCategory.isEquivRel:≣ (of Category:Free Q) = {!!}
isCategory.id (of Category:Free Q) = end
isCategory._◆_ (of Category:Free Q) = comp-QPath
isCategory.unit-l-◆ (of Category:Free Q) {f = f} = {!!} -- ∼-On-refl {p = f}
isCategory.unit-r-◆ (of Category:Free Q) = ∼-On-refl
isCategory.unit-2-◆ (of Category:Free Q) = {!!}
isCategory.assoc-l-◆ (of Category:Free Q) = {!!}
isCategory.assoc-r-◆ (of Category:Free Q) = {!!}
isCategory._◈_ (of Category:Free Q) = {!!}
-- //

-}


{-

-- | Here we begin to build the adjunction.
module _ {Q : Quiver 𝑖} {R : Quiver 𝑗} (F : QuiverHom Q R) where
  map-Category:Free/map : {a b : ⟨ Q ⟩} (f : QPathStr Q a b) -> QPathStr R (⟨ F ⟩ a) (⟨ F ⟩ b)
  map-Category:Free/map end = end
  map-Category:Free/map (fs , f) = map-Category:Free/map fs , qmap f

  map-Category:Free : (Functor (Category:Free Q) (Category:Free R))
  ⟨ map-Category:Free ⟩ = ⟨ F ⟩
  IFunctor.map (of map-Category:Free) = map-Category:Free/map
  IFunctor.functoriality-id (of map-Category:Free) = {!!}
  IFunctor.functoriality-◆ (of map-Category:Free) = {!!}

instance
  IFunctor:Category:Free : IFunctor (⌘ Quiver 𝑖) (⌘ Category _) Category:Free
  IFunctor.map IFunctor:Category:Free = map-Category:Free
  IFunctor.functoriality-id IFunctor:Category:Free = {!!}
  IFunctor.functoriality-◆ IFunctor:Category:Free = {!!}

Functor:Category:Free : Functor (⌘ Quiver 𝑖) (⌘ Category _)
Functor:Category:Free = functor Category:Free

instance
  INotation:Free:Category : INotation:Free (Quiver 𝑖) (Category _)
  INotation:Free.Free INotation:Free:Category = Category:Free


lsum : 𝔏 ^ 3 -> 𝔏 ^ 3
lsum J = ⨆ J , ⨆ J , ⨆ J

lrepeat : 𝔏 -> 𝔏 ^ 3
lrepeat l = l , l , l

⟨_⟩-Hom : (Q : Category 𝑖) -> (a b : ⟨ Q ⟩) -> 𝒰 (𝑖 ⌄ 1)
⟨_⟩-Hom Q a b = Hom a b

module _ {Q : 𝒰 𝑖} {{QC : isCategory Q 𝑗}} where
  Q2 = Category:Free (ForgetCategory (⌘ Q))

  map-eval : {a b : Q} (f : ⟨ Q2 ⟩-Hom a b) -> ⟨ ⌘ Q ⟩-Hom a b
  map-eval end = id
  map-eval (f , x) = map-eval f ◆ x


embed-Category:Free : Natural id-Cat (comp-Cat (Functor:Category:Free {𝑖 = lrepeat 𝑖}) map-Category:FreeorgetCategory)
⟨ ⟨ embed-Category:Free ⟩ {x = x} ⟩ a = a
IQuiverHom.qmap (of (⟨ embed-Category:Free ⟩ {x = x})) e = end , e
of embed-Category:Free = {!!}

eval-Category:Free : Natural (comp-Cat map-Category:FreeorgetCategory (Functor:Category:Free {𝑖 = lrepeat 𝑖})) id-Cat
⟨ ⟨ eval-Category:Free ⟩ ⟩ a = a
IFunctor.map (of ⟨ eval-Category:Free ⟩) f = map-eval f
IFunctor.functoriality-id (of ⟨ eval-Category:Free ⟩) = {!!}
IFunctor.functoriality-◆ (of ⟨ eval-Category:Free ⟩) = {!!}
of eval-Category:Free = {!!}


instance
  IAdjoint:FreeForget : Functor:Category:Free {𝑖 = lrepeat 𝑖} ⊣ map-Category:FreeorgetCategory {𝑖 = lrepeat 𝑖}
  IAdjoint.embed IAdjoint:FreeForget = embed-Category:Free
  IAdjoint.eval IAdjoint:FreeForget = eval-Category:Free

-}

{-

instance
  ILiftHom:FunctorFree : ∀{C : Quiver 𝑖} {D : Category 𝑗} -> ILiftHom (Category:Free (Quiver:LiftQuiver C {joinL 𝑖 𝑗})) (Category:LiftCategory D {joinL 𝑖 𝑗}) (Functor (Category:Free C) D)
  ⟨ ⟨ ILiftHom.liftHom ILiftHom:FunctorFree ⟩ F ⟩ (lift x) = lift (⟨ F ⟩ x)
  of (⟨ ILiftHom.liftHom ILiftHom:FunctorFree ⟩ F) = {!!}
  ⟨ IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:FunctorFree)) F ⟩ x = lower (⟨ F ⟩ (lift x))
  of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:FunctorFree)) F) = {!!}
  IIso-𝒰./⟲ (of (ILiftHom.liftHom ILiftHom:FunctorFree)) = {!!}
  IIso-𝒰./⟳ (of (ILiftHom.liftHom ILiftHom:FunctorFree)) = {!!}
  -- ⟨ ⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F ⟩ (lift x) = lift (⟨ F ⟩ x)
  -- IFunctor.map (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) (lift f) = lift (map f)
  -- IFunctor.functoriality-id (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) = {!!}
  -- IFunctor.functoriality-◆ (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) = {!!}
  -- ⟨ IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G ⟩ x = lower (⟨ G ⟩ (lift x))
  -- IFunctor.map (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) f = lower (map (lift f))
  -- IFunctor.functoriality-id (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) = {!!}
  -- IFunctor.functoriality-◆ (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) = {!!}
  -- IIso-𝒰./⟲ (of (ILiftHom.liftHom ILiftHom:Functor)) = {!!}
  -- IIso-𝒰./⟳ (of (ILiftHom.liftHom ILiftHom:Functor)) = {!!}


-}
