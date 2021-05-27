
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Homotopy.Level where

open import Verification.Conventions
open import Verification.Core.Category.Definition
-- open import Verification.VHM3.Core.Category.Limit



record IHType (n : ℕ) {𝑖} (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field hlevel : isOfHLevel n A
open IHType {{...}} public
unquoteDecl HType htype = #struct "HType" (quote IHType) "A" HType htype

record IHTypeHom {n : ℕ} (A : HType n 𝑖) (B : HType n 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  targethlevel : isOfHLevel n ⟨ B ⟩
  targethlevel = hlevel {{of B}}
open IHTypeHom {{...}} public
unquoteDecl HTypeHom htypeHom = #struct "HTypeHom" (quote IHTypeHom) "f" HTypeHom htypeHom

instance
  typehom:trivial : ∀{A B : HType n 𝑖} -> {F : ⟨ A ⟩ -> ⟨ B ⟩} -> IHTypeHom A B F
  typehom:trivial = record {}

record IHTypeHomEq {n : ℕ} {A : HType n 𝑖} {B : HType n 𝑗} (f g : HTypeHom A B) (p : ⟨ f ⟩ ≡ ⟨ g ⟩) : 𝒰 (𝑖 ､ 𝑗) where
unquoteDecl HTypeHomEq htypeHomEq = #struct "HTypeHomEq" (quote IHTypeHomEq) "p" HTypeHomEq htypeHomEq

instance
  typehomeq:trivial : ∀{A B : HType n 𝑖} -> {F G : HTypeHom A B} -> {p : ⟨ F ⟩ ≡ ⟨ G ⟩} -> IHTypeHomEq F G p
  typehomeq:trivial = record {}

module _ {n : ℕ} {A : 𝒰 𝑖} {{_ : IHType n A}} where
  fillPath : ∀{m} -> {{_ : n ≤-ℕ-Dec m}} -> isOfHLevel m A
  fillPath {m = m} {{P}} = {!!}

record IHTypeFamily (n : ℕ) {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑗 ､ 𝑖) where
  field hlevels : ∀(a : A) -> isOfHLevel n (B a)
open IHTypeFamily {{...}} public

unquoteDecl HTypeFamily htypeFamily = #struct "HTypeFam" (quote IHTypeFamily) "B" HTypeFamily htypeFamily


-- [Definition]
-- | A type is a proposition if all elements are equal:
IProp : (A : 𝒰 𝑖) -> 𝒰 𝑖
IProp A = IHType 1 A

-- | And it is a set if all paths in it are equal:
ISet : (A : 𝒰 𝑖) -> 𝒰 𝑖
ISet A = IHType 2 A
-- //


record IBaseType (A : 𝒰 𝑖) : 𝒰 𝑖 where


-------------------------
-- === General instances
instance
  I-n-Type:Path : ∀{A : 𝒰 𝑖} {n} {{_ : IHType (suc n) A}} {a b : A} -> IHType n (a ≡ b)
  IHType.hlevel (I-n-Type:Path {n = zero} ⦃ HInstance ⦄ {a = a} {b}) = isProp→isContrPath (hlevel {{HInstance}}) a b
  IHType.hlevel (I-n-Type:Path {n = suc n} ⦃ HInstance ⦄ {a = a} {b}) = hlevel {{HInstance}} a b

--   I-n-Type:Σ : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {n} {{_ : IHType n A}} {{_ : IHTypeFamily n B}} -> IHType n (∑ B)
--   IHType.hlevel (I-n-Type:Σ {n = _}) = isOfHLevelΣ _ (hlevel) (hlevels)

--   I-n-Type:Π : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {n} {{_ : IHTypeFamily n B}} -> IHType n (∏ B)
--   IHType.hlevel (I-n-Type:Π {n = _}) = isOfHLevelΠ _ (hlevels)

--   I-n-TypeFamily:const : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {n} {{_ : IHType n B}} -> IHTypeFamily n (∆ {A = A} B)
--   IHTypeFamily.hlevels I-n-TypeFamily:const a = hlevel

--   I-n-TypeFamily:All : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {n} {{_ : ∀{a : A} -> IHType n (B a)}} -> IHTypeFamily n B
--   I-n-TypeFamily:All = {!!}

--   I-n-Type:suc : ∀{A : 𝒰 𝑖} {n} {{_ : IBaseType A}} {{_ : IHType n A}} -> IHType (suc n) A
--   IHType.hlevel I-n-Type:suc = isOfHLevelSuc _ hlevel

-------------------------
-- === instances for types
instance
  I-2-Type:ℕ : IHType 2 ℕ
  IHType.hlevel I-2-Type:ℕ = isSetℕ

  I-1-Type:𝟘-𝒰 : IHType 1 𝟘-𝒰
  IHType.hlevel I-1-Type:𝟘-𝒰 = isProp⊥


byFirstP : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {{_ : ∀{a : A} -> IHType 1 (B a)}}
           -> {a1 a2 : A} {b1 : B a1} {b2 : B a2} -> (p : a1 ≡ a2)
           -> PathP (λ i -> ∑ λ (a : A) -> B a) (a1 , b1) (a2 , b2)
byFirstP {A = A} {B} {{P}} {a1} {a2} {b1} {b2} p =
  let b1' = transport (λ i -> B (p i)) b1
      P1 : b1' ≡ b2
      P1 = hlevel {{P}} b1' b2
      P2 : PathP (λ i -> (B (p i))) b1 b1'
      P2 = transport-filler (λ i -> (B (p i))) b1
      P3 : PathP (λ j → trans-Path (λ i → B (p i)) (λ i → B a2) j) b1 b2
      P3 = compPathP P2 P1
      P4 : trans-Path (λ i → B (p i)) (λ i → B a2) ≡ (λ i -> B (p i))
      P4 = sym-Path (rUnit (λ i -> B (p i)))
      P5 : PathP (λ i → B (p i)) b1 b2
      P5 = transport (λ k -> PathP (λ i -> P4 k i) b1 b2) P3
  in λ i -> p i , P5 i


{-
level-Set : ∀{A : 𝒰 𝑖} {{_ : ISet A}} -> isSet A
level-Set {{AInst}} = hlevel {{AInst}}

fillUnique_Path : ∀{A : 𝒰 𝑖} -> (n : ℕ) -> {{_ : IHType n A}} -> isOfHLevel n A
fillUnique_Path n = hlevel {n = n}


-- test5 : (a b : ℕ) (p q : a ≡ b) -> p ≡ q
-- test5 a b p q = hlevel-Set {A = ℕ} a b p q
-}
