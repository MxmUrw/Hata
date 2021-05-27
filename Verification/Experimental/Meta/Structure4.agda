
module Verification.Experimental.Meta.Structure4 where

open import Verification.Conventions hiding (⟪_⟫ ; Structure ; ′_′)
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)


-- record Structure {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
--   constructor str
--   field ⟨_⟩ : A
--         {of_} : P ⟨_⟩
--         -- of_ : P ⟨_⟩


  -- infixr 2 of_

record ∑i_ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  instance constructor make∑i
  -- field overlap {{ifst}} : A
  field {ifst} : A
  field overlap {{isnd}} : B (ifst)
open ∑i_ {{...}} public

record hasU (A : 𝒰 𝑖) 𝑗 𝑘 : 𝒰 (𝑗 ⁺ ､ 𝑘 ⁺) where
  field getU : 𝒰 𝑗
  field getP : getU -> 𝒰 𝑘

open hasU public

record hasU2 {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) 𝑙 𝑘 : 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ⁺ ､ 𝑘 ⁺) where
  field getU2 : A -> 𝒰 𝑙
        getP2 : ∀{a : A} -> getU2 a -> 𝒰 𝑘
        reconstruct : ∀{a} -> (∑ getP2 {a}) -> P a
open hasU2 public

_on2_ : {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) {{U : hasU2 P 𝑙 𝑘}} -> (a : A) -> {{_ : getU2 U a}} -> 𝒰 _
_on2_ P {{U}} a = getP2 U {a = a} it

-- _on_ : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} -> (a : getU U) -> 𝒰 _
-- _on_ UU {{U}} a = getP U a

record _:>_ {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) {{U : hasU2 P 𝑖₁ 𝑗₁}} (Q : (a : A) -> {{_ : P a}} -> 𝒰 𝑘)
            (a : A) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑖₁ ､ 𝑗₁) where
  constructor make:>
  field {⟪_⟫} : getU2 U a
  field {Proof1} : getP2 U ⟪_⟫
  field overlap {{Proof2}} : Q a {{reconstruct U (⟪_⟫ , Proof1)}}

infixl 50 _:>_

record From (A : 𝒰 𝑖) (a : A) : 𝒰₀ where

record isAnything {A : 𝒰 𝑖} (a : A) : 𝒰₀ where

instance
  From:Any : ∀{A : 𝒰 𝑖} {a : A} -> From A a
  From:Any = record {}

instance
  isAnything:anything : {A : 𝒰 𝑖} {a : A} -> isAnything a
  isAnything:anything = record {}

instance
  hasU2:From : ∀{A : 𝒰 𝑖} -> hasU2 (From A) _ _
  getU2 (hasU2:From {A = A}) = From A
  getP2 (hasU2:From {A = A}) = isAnything
  reconstruct (hasU2:From {A = A}) x = record {}


instance
  hasU2:> : {A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} {{U : hasU2 P 𝑖₁ 𝑗₁}} {Q : (a : A) -> {{_ : P a}} -> 𝒰 𝑘} -> hasU2 (P :> Q) _ _
  getU2 (hasU2:> {A = A} {P} ⦃ U ⦄ {Q}) = getU2 U
  getP2 (hasU2:> {A = A} {P} ⦃ U ⦄ {Q}) a = ∑i λ (p1 : getP2 U a) -> Q _ {{reconstruct U (_ , p1)}}
  reconstruct (hasU2:> {A = A} {P} ⦃ U ⦄ {Q}) (a , pa) = make:> {⟪_⟫ = a} {pa .ifst} {{pa .isnd}}

-- {UU : 𝒰 𝑖} {{U : hasU2 UU 𝑘 𝑙}} {P : UU -> 𝒰 𝑗} -> hasU (UU :& P) _ _

-- instance
--   hasU:∑i : ∀{A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} -> hasU (∑i P) _ _
--   getU (hasU:∑i {A = A} {P}) = A
--   getP (hasU:∑i {A = A} {P}) = P


{-
record _:>>_ {A : 𝒰 𝑖} {P0 : A -> 𝒰 𝑖₁} (P : (a : A) -> {{_ : P0 a}} -> 𝒰 𝑗) (Q : (a : A) -> {{_ : (P0 :> P) a}} -> 𝒰 𝑘) (a : A) {{_ : P0 a}} : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field {{Proof1}} : P a
  field {{Proof2}} : Q a

infixl 50 _:>>_


record ∑i_ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  instance constructor make∑i
  -- field overlap {{ifst}} : A
  field {ifst} : A
  field overlap {{isnd}} : B (ifst)
open ∑i_ {{...}} public

record ∑p (𝑖 : 𝔏) {𝑘 𝑗 : 𝔏} {A : 𝒰 𝑖} {Q : A -> 𝒰 𝑘} (B : (a : A) -> {{_ : Q a}} -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  instance constructor make∑p
  -- field overlap {{ifst}} : A
  -- field {ifst} : A
  -- field overlap {{isnd}} : B (ifst)
open ∑p {{...}} public




-}


record Structure {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) {{U : hasU2 P 𝑙 𝑘}} : 𝒰 (𝑖 ､ 𝑘 ､ 𝑙) where
  constructor ′_′
  field ⟨_⟩ : A
        {Proof3-useless} : getU2 U ⟨_⟩
        {Proof3} : getP2 U Proof3-useless

open Structure public

-- ′_′ : {A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} -> (a : A) -> {{_ : P a}} -> Structure P
-- ′_′ a {{X}} = str a {_} {X}

-- ′_′ : {A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} -> (a : A) -> {{_ : P a}} -> Structure P
-- ′_′ a {{X}} = str a {_} {X}



instance
  hasU:Structure : ∀{A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} {{_ : hasU2 P 𝑙 𝑘}} -> hasU (Structure P) _ _
  getU (hasU:Structure {A = A} {P}) = A
  getP (hasU:Structure {A = A} {P}) = P

_on_ : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} -> (a : getU U) -> 𝒰 _
_on_ UU {{U}} a = getP U a

is_ : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} -> (a : getU U) -> 𝒰 _
is_ UU {{U}} a = getP U a

infixl 100 is_
{-

record _:,_ {U : 𝒰 𝑖} {R : U -> 𝒰 𝑖₂} (P : (a : U) -> {{_ : R a}} -> 𝒰 𝑗) (Q : (a : U) -> {{_ : R a}} -> 𝒰 𝑗₂) (a : U) {{_ : R a}} : 𝒰 (𝑗 ､ 𝑗₂) where
  constructor make,
  field overlap {{Proof1}} : P a
  field overlap {{Proof2}} : Q a

infixr 80 _:,_


--------------------------------------------------
-- Testcase
-}


-- record hasU2 {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) 𝑙 𝑘 : 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ⁺ ､ 𝑘 ⁺) where

module TEST where
  private

    record isTypoid 𝑗 A {{_ : From (𝒰 𝑖) A}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
      field _∼_ : A -> A -> 𝒰 𝑗
    open isTypoid {{...}} public

    -- Typoid : ∀(𝑖 : 𝔏 ^ 2) -> 𝒰 _
    -- Typoid 𝑖 = Structure (isType (𝑖 ⌄ 0) :> isTypoid (𝑖 ⌄ 1))

    Typoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
    Typoid 𝑗 = Structure (From (𝒰 (𝑗 ⌄ 0)) :> isTypoid (𝑗 ⌄ 1))

    -- record isMonoid (A : 𝒰 _) {{_ : Typoid 𝑖 on A}} : 𝒰 (𝑖) where
    record isMonoid (A : 𝒰 _) {{_ : (From (𝒰 𝑖) :> isTypoid 𝑗) A }} : 𝒰 (𝑖) where
      field _⋆_ : A -> A -> A
    -- record isMonoid A {{_ : (isType 𝑖 :> isTypoid) A}} : 𝒰 (𝑖) where
    open isMonoid {{...}} public

    -- strOf : {A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} {{_ : hasU2 P 𝑙 𝑘}} -> {a : A} -> (_ : )

    Monoid : ∀(𝑖 : 𝔏 ^ 2) -> 𝒰 _
    Monoid 𝑖 = Structure (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid)
    -- ((is Typoid 𝑖 :> isMonoid) on2_)

{-
    -- ∑p (𝑖 ⁺) {𝑘 = 𝑖} {Q = isTypoid} isMonoid
    -}

    record isCommutative A {{_ : (is Monoid 𝑖) A}} : 𝒰 (𝑖 ､ 𝑗) where
      field comm-⋆ : ∀{a b : A} -> (a ⋆ b) ∼ (b ⋆ a)
    open isCommutative {{...}} public

{-
    record isGroup A {{_ : Monoid 𝑖 on A}} : 𝒰 𝑖 where
      field ◡_ : A -> A

{-
    Group : ∀(𝑖) -> 𝒰 _
    Group 𝑖 = Structure ((Monoid 𝑖 on_) :> isGroup)


    record isSemiring (A : 𝒰 _) {{_ : (is Monoid 𝑖 :> isCommutative) A}} : 𝒰 𝑖 where
      field _⋅_ : A -> A -> A

    Semiring : ∀(𝑖) -> 𝒰 _
    Semiring 𝑖 = Structure (_ :> isSemiring {𝑖 = 𝑖})

    record isRing (A : 𝒰 _) {{_ : (is Monoid 𝑖 :> ((isCommutative :>> isSemiring) :, isGroup)) A}} : 𝒰 𝑖 where

-}
    record isTypoidHom {A B} {{_ : Typoid 𝑖 on A}} {{_ : Typoid 𝑗 on B}} f {{_ : (From (A -> B)) f}} : 𝒰 (𝑖 ､ 𝑗) where
      field preserves-∼ : ∀{a b : A} -> a ∼ b -> f a ∼ f b

    TypoidHom : (A : Typoid 𝑖) (B : Typoid 𝑗) -> 𝒰 _
    TypoidHom A B = Structure (_ :> isTypoidHom {{of A}} {{of B}})

    -- record isTypoidHom (A : Typoid 𝑖) (B : Typoid 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    --   field preserves-∼ : ∀{a b : ⟨ A ⟩} -> a ∼ b -> f a ∼ f b

    -- TypoidHom : (A : Typoid 𝑖) (B : Typoid 𝑗) -> 𝒰 _
    -- TypoidHom A B = Structure (isTypoidHom A B)

    record isMonoidHom {A B} {{_ : Monoid 𝑖 on A}} {{_ : Monoid 𝑗 on B}} (f : A -> B) {{_ : (_ :> isTypoidHom) f}} : 𝒰 (𝑖 ､ 𝑗) where

    -- record isMonoidHom (A : Monoid 𝑖) (B : Monoid 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) {{_ : TypoidHom (′ ⟨ A ⟩ ′) (′ ⟨ B ⟩ ′) on f}} : 𝒰 (𝑖 ､ 𝑗) where

    MonoidHom : (A : Monoid 𝑖) (B : Monoid 𝑗) -> 𝒰 _
    MonoidHom A B = Structure (_ :> isMonoidHom {{of A}} {{of B}})

{-
{-


    record isGroupHom {A B} {{_ : Group 𝑖 on A}} {{_ : Group 𝑗 on B}} (f : A -> B) {{_ : (_ :> isMonoidHom) f}} : 𝒰 (𝑖 ､ 𝑗) where

-}
    -- record isMonoidHom (A : Monoid 𝑖) (B : Monoid 𝑗) f {{_ : TypoidHom (⌘ ⟨ A ⟩) (⌘ ⟨ B ⟩) on f}} : 𝒰 (𝑖 ､ 𝑗) where

    -- record isCommutative (A : 𝒰 𝑖) {{_ : (isTypoid :> isMonoid) A}} : 𝒰 𝑖 where


-}

-}

