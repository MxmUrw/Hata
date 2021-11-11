
{-# OPTIONS --cubical --allow-unsolved-metas --no-import-sorts #-}

module Verification.Old.Core.Category.Instance.Set.Equalizers where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Functor.Adjunction
open import Verification.Old.Core.Category.Limit.Kan.Definition
open import Verification.Old.Core.Category.Limit.Kan.Terminal
open import Verification.Old.Core.Category.Limit.Kan.Equalizer
open import Verification.Old.Core.Category.Instance.SmallCategories
-- open import Verification.Old.Core.Category.Limit.Definition
-- open import Verification.Old.Core.Category.Limit.Product
-- open import Verification.Old.Core.Category.Limit.Equalizer
-- open import Verification.Old.Core.Category.Monad
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.Instance.Set.Definition
open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Homotopy.Level



--------------------------------------------------------------------
-- Eualizers



record _=?=-Set_ {A : Set 𝑖} {B : Set 𝑗} (f g : HTypeHom A B) : 𝒰 (𝑖 ､ 𝑗) where
  constructor _,_
  field fst : ⟨ A ⟩
        snd : ⟨ f ⟩ fst ≡ ⟨ g ⟩ fst
open _=?=-Set_ public


-- _=?=-Set_ : {A : Set 𝑖} {B : Set 𝑗} -> (f g : HTypeHom A B) -> Set (𝑖 ､ 𝑗)
-- ⟨ f =?=-Set g ⟩ = ∑ λ a -> ⟨ f ⟩ a ≡ ⟨ g ⟩ a
-- IHType.hlevel (of (_=?=-Set_  {A = A} {B} f g)) = isOfHLevelΣ 2 (hlevel {{of A}}) (λ x -> isOfHLevelSuc 1 (hlevel {{of B}} _ _))


byFirst1 : {A : Set 𝑖} {B : Set 𝑗} -> {f g : HTypeHom A B} -> {a b : f =?=-Set g} -> fst a ≡ fst b -> a ≡ b
byFirst1 {A = A}{B}{f}{g}{a}{b} p i = p i , isSet→isSet' (hlevel {{of B}}) (snd a) (snd b) (cong ⟨ f ⟩ (p)) (cong ⟨ g ⟩ (p)) i

_Set:=?=-Set_ : {A : Set 𝑖} {B : Set 𝑗} -> (f g : HTypeHom A B) -> Set (𝑖 ､ 𝑗)
⟨ f Set:=?=-Set g ⟩ = f =?=-Set g
IHType.hlevel (of (_Set:=?=-Set_ {A = A} {B = B} f g)) _ _ p q = {!!}
--   let P : (cong fst p) ≡ (cong fst q)
--       P = hlevel {{of A}} _ _ _ _

--       Q : p ≡ q
--       Q i j = P i j , hlevel {{of B}} _ _ {!!} {!!} j

--   in Q
-- byFirst1 (hlevel {{of A}} _ _ (cong fst p) (cong fst q)) i


module _ where
  private

  --------------------------------------------------------------------
  -- Defining the equalizer functor

    E : Functor (` 𝔼 ⟶ ` Set 𝑖 ` `) (` 𝟙 ⟶ ` Set 𝑖 ` `)
    ⟨ E {𝑖} ⟩ F = free-Diagram-Lift f

      where f : QuiverHom (` 𝟙-𝒰 `) (ForgetCategory ` Set _ `)
            ⟨ f ⟩ _ = ((map {{of F}} ` arr₀ `) Set:=?=-Set (map {{of F}} ` arr₁ `))
            IQuiverHom.qmap (of f) e = ′ (λ x -> x) ′

    IFunctor.map (of E) α = free-Diagram-Nat f (λ {()})
      where f = λ {_ -> ′( λ {(x , xp) -> ⟨ ⟨ α ⟩ ⟩ x ,
                    let P : ⟨ (⟨ α ⟩ ◆ map _) ⟩ x ≡ ⟨ (⟨ α ⟩ ◆ map _) ⟩ x
                        P = ((naturality _ x)) ∙ cong ⟨ ⟨ α ⟩ ⟩ xp ∙ ( (naturality _ x ⁻¹))
                    in P})′}

    IFunctor.functoriality-id (of E) {a = a} α _ = byFirst1 refl
    IFunctor.functoriality-◆ (of E) {a = a} {b} {c} x _ = byFirst1 refl
    IFunctor.functoriality-≣ (of E) p _ x = byFirst1 (p _ (fst x))


  --------------------------------------------------------------------
  -- Proving adjointness

  ----------------------------
  -- The counit
    ε : ∀(x : 𝔼 ⟶ ` Set 𝑖 `) -> ∀(a : Pair) -> (⟨ ⟨ ! 𝔼 * ⟩ (⟨ E ⟩ x) ⟩ (↥ a)) ⟶ ⟨ x ⟩ (↥ a)
    ε x ₀ = ′ (λ (a , p) -> a) ′
    ε x ₁ = ′ (λ (a , p) -> ⟨ map {{of x}} ` arr₀ ` ⟩ a) ′

    εp : ∀{𝑖} -> ∀(x : 𝔼 ⟶ (⩚ Set 𝑖)) -> ∀{a b : Pair} -> (e : Edge {{of Quiver:Pair}} a b)
        -> ε x a ◆ map ` e ` ≣ map {{of (⟨ ! 𝔼 * ⟩ (⟨ E ⟩ x))}} ` e ` ◆ ε x b
    εp x {₀} {₁} arr₀ _ = refl
    εp x {₀} {₁} arr₁ (y , yp) =  let
                                      P : (⟨ map {{of x}} (` arr₁ `) ⟩ y) ≡ (⟨ map {{of x}} (` arr₀ `) ⟩ y)
                                      P = yp ⁻¹
                                  in P

    ε' : ∀(x : 𝔼 ⟶ ` Set 𝑖 `) -> Natural (⟨ E ◆ ! 𝔼 * ⟩ x) x
    ε' x = free-Diagram-Nat (ε x) (εp x)


    ----------------------------
    -- The unit
    η : ∀(x : 𝟙 ⟶ ` Set 𝑖 `) -> ∀(a : 𝟙-𝒰) -> ⟨ x ⟩ (↥ a) ⟶ (⟨ ⟨ E ⟩ (⟨ ! 𝔼 * ⟩ x) ⟩ (↥ a))
    η _ = λ _ -> ′ (λ {a -> (a , refl)}) ′

    η' : ∀(x : 𝟙 ⟶ ` Set 𝑖 `) -> Natural x (⟨ ! 𝔼 * ◆ E ⟩ x)
    η' x = free-Diagram-Nat (η x) (λ {()})

  ----------------------------
  -- putting it together

  -- [Theorem]
  -- | Finally we can show that |Eq| is a right adjoint. [...]
  instance
    lem::1 : (! 𝔼 *) ⊣ E {𝑖 = 𝑖}

    -- | For this, we use the |η| and |ε| defined before, and set the following:
    ⟨ IAdjoint.embed lem::1 ⟩ {x = x} = η' x

    INatural.naturality (of IAdjoint.embed lem::1) f x _ = byFirst1 refl

    ⟨ IAdjoint.eval lem::1 ⟩ {x = x} = ε' x

    INatural.naturality (of IAdjoint.eval lem::1) α (↥ ₀) _ = refl
    INatural.naturality (of IAdjoint.eval lem::1) {x = a} {b} α (↥ ₁) (x , xp) =
                            let P : ⟨ ⟨ α ⟩ ⟩ (⟨ map {{of a}} ` arr₀ ` ⟩ x) ≡ ⟨ map {{of b}} ` arr₀ ` ⟩ (⟨ ⟨ α ⟩ ⟩ x)
                                P = naturality {{of α}} (` arr₀ `) x ⁻¹
                            in P

    IAdjoint.reduce-Adj-β lem::1 (↥ ₀) _ = refl
    IAdjoint.reduce-Adj-β lem::1 {a = a} (↥ ₁) x = functoriality-id {{of a}} x
    IAdjoint.reduce-Adj-η lem::1 (↥ tt) _ = byFirst1 refl

    lem::2 : hasEqualizers ` Set 𝑖 `
    ⟨ lem::2 ⟩ = E
    of lem::2 = lem::1
    -- //


-- Evaluating reduce-β by hand...
-- even though agda can show it...
      -- let -- P : ⟨ (map {{of ! 𝔼 *}} (η' a) ◆ ε' (⟨ ! 𝔼 * ⟩ a)) ⟩ {↥ ₁} ≣ id
      --     -- P = {!!}
      --     -- Q : ⟨ map {{of ! 𝔼 *}} (η' a) ⟩ {↥ ₁} ◆ ⟨ ε' (⟨ ! 𝔼 * ⟩ a) ⟩ {↥ ₁} ≣ id
      --     -- Q = {!!}

      --     -- Q' : ⟨ ⟨ map {{of ! 𝔼 *}} (η' a) ⟩ {↥ ₁} ◆ ⟨ ε' (⟨ ! 𝔼 * ⟩ a) ⟩ {↥ ₁} ⟩ ≡ id {{of Category:𝒰 _}}
      --     -- Q' = {!!}

      --     -- Q'' : ⟨ ⟨ map {{of ! 𝔼 *}} (η' a) ⟩ {↥ ₁} ⟩ ◆ ⟨ ⟨ ε' (⟨ ! 𝔼 * ⟩ a) ⟩ {↥ ₁} ⟩ ≡ id {{of Category:𝒰 _}}
      --     -- Q'' = {!!}

      --     -- Q''' : ∀ x -> ⟨ ⟨ ε' (⟨ ! 𝔼 * ⟩ a) ⟩ {↥ ₁} ⟩ (⟨ ⟨ map {{of ! 𝔼 *}} (η' a) ⟩ {↥ ₁} ⟩ x) ≡ x
      --     -- Q''' = {!!}

      --     -- Q'''' : ∀ x -> ⟨ map {{of (⟨ ! 𝔼 * ⟩ a)}} ` arr₀ ` ⟩ (fst (⟨ ⟨ map {{of ! 𝔼 *}} (η' a) ⟩ {↥ ₁} ⟩ x)) ≡ x
      --     -- Q'''' = {!!}

      --     -- Q''''' : ∀ x -> ⟨ map {{of (⟨ ! 𝔼 * ⟩ a)}} ` arr₀ ` ⟩ (fst (⟨ ⟨ η' a ⟩ { ⟨ (! 𝔼) ⟩ (↥ ₁)} ⟩ x)) ≡ x
      --     -- Q''''' = {!!}

      --     -- Q'''''' : ∀ x -> ⟨ map {{of (⟨ ! 𝔼 * ⟩ a)}} ` arr₀ ` ⟩ (fst (⟨ ⟨ η' a ⟩ { (↥ tt)} ⟩ x)) ≡ x
      --     -- Q'''''' = {!!}

      --     -- Q''''''' : ∀ x -> ⟨ map {{of (! 𝔼 ◇ a)}} ` arr₀ ` ⟩ (x) ≡ x
      --     -- Q''''''' = {!!}

      --     -- Q'''''''' : ∀ x -> ⟨ map {{of a}} (map {{of ! 𝔼}} ` arr₀ `) ⟩ (x) ≡ x
      --     -- Q'''''''' = {!!}

      --     -- Q''''''''' : ∀ x -> ⟨ map {{of a}} (id {{of 𝟙}}) ⟩ (x) ≡ x
      --     -- Q''''''''' = {!!}
      --     aa : ℕ
      --     aa = 1

      -- in functoriality-id {{of a}}

