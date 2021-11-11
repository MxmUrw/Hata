

module Verification.Core.Meta.Structure5 where

open import Verification.Conventions hiding (⟪_⟫ ; Structure ; ′_′)
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)

record Structure {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor ′_′
  field ⟨_⟩ : A
  field overlap {{of_}} : P ⟨_⟩
open Structure public

record From (A : 𝒰 𝑖) (a : A) : 𝒰₀ where

-- instance
module _ where
  From:Any : ∀{A : 𝒰 𝑖} {a : A} -> From A a
  From:Any = record {}

record _:>_ {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) (Q : (a : A) -> {{_ : P a}} -> 𝒰 𝑘) (a : A) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  constructor make:>
  field overlap {{Proof1}} : P a
  field overlap {{Proof2}} : Q a

infixl 50 _:>_

record _:>>_ {A : 𝒰 𝑖} {P0 : A -> 𝒰 𝑖₁} (P : (a : A) -> {{_ : P0 a}} -> 𝒰 𝑗) (Q : (a : A) -> {{_ : (P0 :> P) a}} -> 𝒰 𝑘) (a : A) {{_ : P0 a}} : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field overlap {{Proof1}} : P a
  field overlap {{Proof2}} : Q a {{make:>}}


-- record _:>2_ {U : 𝒰 𝑖} {R : U -> 𝒰 𝑖₂} (P : (a : U) -> {{_ : R a}} -> 𝒰 𝑗) (Q : (a : U) -> {{_ : R a}} -> 𝒰 𝑗₂) (a : U) {{_ : R a}} : 𝒰 (𝑗 ､ 𝑗₂) where

record _:,_ {U : 𝒰 𝑖} {R : U -> 𝒰 𝑖₂} (P : (a : U) -> {{_ : R a}} -> 𝒰 𝑗) (Q : (a : U) -> {{_ : R a}} -> 𝒰 𝑗₂) (a : U) {{_ : R a}} : 𝒰 (𝑖 ､ 𝑖₂ ､ 𝑗 ､ 𝑗₂) where
  constructor make,
  field overlap {{Proof1}} : (R :> P) a
  field overlap {{Proof2}} : (R :> Q) a


--------------------------------------------------
-- `On`-functionality

record hasU (A : 𝒰 𝑖) 𝑗 𝑘 : 𝒰 (𝑗 ⁺ ､ 𝑘 ⁺) where
  field getU : 𝒰 𝑗
  field getP : getU -> 𝒰 𝑘
open hasU public

instance
  hasU:Structure : ∀{A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} -> hasU (Structure P) _ _
  getU (hasU:Structure {A = A} {P}) = A
  getP (hasU:Structure {A = A} {P}) = P

_on_ : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} -> (a : getU U) -> 𝒰 _
_on_ UU {{U}} a = getP U a

is_ : (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} -> (a : getU U) -> 𝒰 _
is_ UU {{U}} a = getP U a

infixl 100 is_

--------------------------------------------------
-- Testcase


-- record hasU2 {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) 𝑙 𝑘 : 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ⁺ ､ 𝑘 ⁺) where

module TEST where
  private

    record isTypoid 𝑗 A {{_ : From (𝒰 𝑖) A}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
      field _∼_ : A -> A -> 𝒰 𝑗
    open isTypoid {{...}} public

    -- Typoid : ∀(𝑖 : 𝔏 ^ 2) -> 𝒰 _
    -- Typoid 𝑖 = Structure (isType (𝑖 ⌄ 0) :> isTypoid (𝑖 ⌄ 1))

    -- Typoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
    -- Typoid 𝑗 = Structure (From (𝒰 (𝑗 ⌄ 0)) :> isTypoid (𝑗 ⌄ 1))

    record isMonoid (A : 𝒰 _) {{_ : (From (𝒰 𝑖) :> isTypoid 𝑗) A }} : 𝒰 (𝑖) where
      field _⋆_ : A -> A -> A
      infixl 40 _⋆_
    -- record isMonoid A {{_ : (isType 𝑖 :> isTypoid) A}} : 𝒰 (𝑖) where
    open isMonoid {{...}} public

    -- strOf : {A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} {{_ : hasU2 P 𝑙 𝑘}} -> {a : A} -> (_ : )

    -- Monoid : ∀(𝑖 : 𝔏 ^ 2) -> 𝒰 _
    -- Monoid 𝑖 = Structure (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid)


    record isCommutative A {{_ : (From (𝒰 𝑖) :> isTypoid 𝑗 :> isMonoid) A}} : 𝒰 (𝑖 ､ 𝑗) where
      field comm-⋆ : ∀{a b : A} -> (a ⋆ b) ∼ (b ⋆ a)
    open isCommutative {{...}} public

    Monoid : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
    Monoid 𝑖 = Structure (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid)

    AbelianMon : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
    AbelianMon 𝑖 = Structure (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid :> isCommutative)

    module TEST2 {A B : AbelianMon 𝑖} where
      myprop : ∀{a b c : ⟨ A ⟩} -> (a ⋆ b ⋆ c ∼ c ⋆ a ⋆ b) -> 𝟙-𝒰
      myprop {a} {b} {c} q =
        let x = comm-⋆ {a = b} {c}
        in tt

    record isGroup {𝑖 : 𝔏 ^ 2} A {{_ : (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid) A}} : 𝒰 𝑖 where
      field ◡_ : A -> A
      infixl 100 ◡_
    open isGroup {{...}} public

    testMonoid : ∀{𝑖 : 𝔏 ^ 2} {A : 𝒰 (𝑖 ⌄ 0)} {{_ : (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid) A}} -> A -> A
    testMonoid a = a ⋆ a ⋆ a

    testGroup : ∀{𝑖 : 𝔏 ^ 2} {A : 𝒰 (𝑖 ⌄ 0)} {{_ : (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid :> isGroup) A}} -> A -> A
    testGroup a = a ⋆ ◡ a

    record isSemiring {𝑖 : 𝔏 ^ 2} A {{_ : (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid :> isCommutative) A}} : 𝒰 𝑖 where
      field _⋅_ : A -> A -> A

    record isRing {𝑖 : 𝔏 ^ 2} (A : 𝒰 (𝑖 ⌄ 0)) {{_ : (From (𝒰 (𝑖 ⌄ 0)) :> isTypoid (𝑖 ⌄ 1) :> isMonoid :> ((isCommutative :>> isSemiring) :, isGroup)) A}} : 𝒰 𝑖 where
      field ⨡ : A
      testval : A
      testval = testGroup ⨡

{-
{-
{-
    Group : ∀(𝑖) -> 𝒰 _
    Group 𝑖 = Structure ((Monoid 𝑖 on_) :> isGroup)



    Semiring : ∀(𝑖) -> 𝒰 _
    Semiring 𝑖 = Structure (_ :> isSemiring {𝑖 = 𝑖})


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



-}




