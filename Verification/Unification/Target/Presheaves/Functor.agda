

module Verification.Unification.Target.Presheaves.Functor where

open import Verification.Conventions
open import Verification.Core.Type
-- open import Verification.Core.Algebra
open import Verification.Core.Order
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Functor.Presheaf
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.Natural
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Type.Coproducts
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Instance.TypeProperties
open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Kan.Definition
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Monad.Definition
open import Verification.Unification.RecAccessible
open import Verification.Core.Homotopy.Level


      -- % https://q.uiver.app/?q=WzAsNixbMCwwLCJUWCJdLFswLDEsIlRUWSJdLFswLDIsIlRZIl0sWzEsMCwiRFRYIl0sWzEsMSwiRFRUWSJdLFsxLDIsIkRUWSJdLFswLDMsIlxcZGVsdGEiXSxbMCwxLCJUZiIsMl0sWzMsNCwiRFRmIl0sWzEsMiwiXFxtdSIsMl0sWzIsNSwiXFxkZWx0YSIsMl0sWzQsNSwiRFxcbXUiXV0=
      -- | Here we do the following:
      -- \[\begin{tikzcd}
      -- 	TX & DTX \\
      -- 	TTY & DTTY \\
      -- 	TY & DTY
      -- 	\arrow["\delta", from=1-1, to=1-2]
      -- 	\arrow["Tf"', from=1-1, to=2-1]
      -- 	\arrow["DTf", from=1-2, to=2-2]
      -- 	\arrow["\mu"', from=2-1, to=3-1]
      -- 	\arrow["\delta"', from=3-1, to=3-2]
      -- 	\arrow["D\mu", from=2-2, to=3-2]
      -- \end{tikzcd}\]
module _ {𝒞 : Category 𝑖} {T : Monad 𝒞} {D : Functor 𝒞 𝒞} (δ : Natural ⟨ T ⟩ (⟨ T ⟩ ◆ D)) where
  module _ {X Y : ⟨ 𝒞 ⟩} (f : X ⟶ ⟨ ⟨ T ⟩ ⟩ Y) (P : commutes-Nat (μ T) δ) where
    private
            T' = ⟨ T ⟩
    naturalJoinCommute : ⟨ δ ⟩ ◆ map (map f ◆ join) ≣ map f ◆ join ◆ ⟨ δ ⟩
    naturalJoinCommute = ⟨ δ ⟩ ◆ map (map f ◆ join)

                         ≣⟨ refl ◈ functoriality-◆ ⟩

                         ⟨ δ ⟩ ◆ (map (map f) ◆ map join)

                         ≣⟨ assoc-r-◆ ⟩

                         ⟨ δ ⟩ ◆ map (map f) ◆ map join

                         ≣⟨ naturality f ◈ refl ⟩

                         map f ◆ ⟨ δ ⟩ ◆ map join

                         ≣⟨ assoc-l-◆ ⟩

                         map f ◆ (⟨ δ ⟩ ◆ map join)

                         ≣⟨ refl ◈ P ⟩

                         map f ◆ (join ◆ ⟨ δ ⟩)

                         ≣⟨ assoc-r-◆ ⟩

                         map f ◆ join ◆ ⟨ δ ⟩       ∎



-- {-# BUILTIN REWRITE _≡_ #-}

--------------------------------------------------------------------
-- == The functor to Recursion Modules
-- | Let A, B, C be sets, and let $T$ be a fixed \AD{RecMonad} in this section.

-- Monoid:Path : Quiver 𝑖 -> Monoid (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1)
-- ⟨ Monoid:Path Q ⟩ = Maybe (∑ λ (x : ⟨ Q ⟩) -> ∑ λ (y : ⟨ Q ⟩) -> Edge {{of Q}} x y)
-- IMonoid.𝟷 (of Monoid:Path Q) = {!!}
-- IMonoid._⋅_ (of Monoid:Path Q) = {!!}
-- IMonoid.assoc-⋅ (of Monoid:Path Q) = {!!}
-- IMonoid.unit-l-⋅ (of Monoid:Path Q) = {!!}
-- IMonoid.unit-r-⋅ (of Monoid:Path Q) = {!!}

-- FFF = Functor:Either 𝟙-𝒰

-- module _ {K : 𝒰 𝑖} (E : K -> K -> 𝒰 𝑗) where
--   data Edge₊ : (a b : Maybe K) -> 𝒰 (𝑖 ､ 𝑗) where
--     edge : ∀ {a b} -> E a b -> Edge₊ (just a) (just b)
--     zedge : ∀{a} -> Edge₊ nothing (just a)


module _ {A : 𝒰 𝑖} {a b : A} (P : isSet A) where
  isSet-Str : ∀(p q : a ≡-Str b) -> p ≡ q
  isSet-Str refl-StrId q =
    let P1 : ≡-Str→≡ q ≡ refl
        P1 = P _ _ _ refl
        P2 : q ≡ refl
        P2 = ≡-change-iso q ⁻¹ ∙ cong ≡→≡-Str P1 ∙ ≡-change-iso refl
    in P2 ⁻¹



module _ {K : 𝒰 𝑖} (T' : Monad `(IdxSet K 𝑖)`) {{_ : IRecAccessible T'}} where
  T = ⟨ T' ⟩
  private
    Q : Quiver (𝑖 , 𝑖 , 𝑖)
    ⟨ Q ⟩ = K
    IQuiver.Edge (of Q) = Edge {{Dir}}
    --Maybe (Edge {{Dir}} a b)
    IQuiver._≈_ (of Q) = _≡_
    IQuiver.isEquivRelInst (of Q) = isEquivRel:Path

  𝔇 = (Category:Free Q)

  instance _ = of 𝔇
  instance _ = of Q
  instance _ = of T
  instance _ = of T'

  Mod : IdxSet K 𝑖 -> K -> Set 𝑖
  ⟨ Mod X k ⟩ = ∑ λ j -> Hom {{of 𝔇}} k j ×-𝒰 ⟨ ⟨ T ⟩ X ⟩ j
  of Mod X k = {!!}


  private
    data isNormal {A : IdxSet K 𝑖} : ∀{k} -> ⟨ Mod A k ⟩ -> 𝒰 (𝑖) where
      by-id : ∀{k} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ k} -> isNormal (_ , id-Q , a)
      by-nothing : ∀{k j} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ j} -> (e : Edge {{of Q}} k j) -> δ a e ≡-Str nothing -> isNormal (_ , some (last e) , a)
      by-later : ∀{j k₁ k₂} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ j} -> (p : QPath {{of Q}} k₂ j) -> (e : Edge {{of Q}} k₁ k₂) -> isNormal (_ , some p , a) -> isNormal (_ , some (e ∷ p) , a)

      -- by-[] : ∀{a : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ A ⟩ k} -> isNormal (_ , id-Q , a)
      -- by-eval : ∀{j} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ j} -> {a' : ⟨ A ⟩ j} -> ⟨ ⟨ decompose ⟩ ⟩ _ a ≡-Str left a'
      --            -> (p : Hom k j) -> isNormal (_ , p , right a)

        -- by-[] : ∀{a : ⟨ T ⟩ A} -> (depth a ≡ 0 -> 𝟘-𝒰) -> isNormal ([] , a)
        -- by-depth : ∀{ds} -> ∀{a : ⟨ T ⟩ A} -> depth a ≡ 0 -> isNormal (ds , a)

    lem-10 : ∀{A : IdxSet K 𝑖} {k} {a : ⟨ Mod A k ⟩} -> isProp (isNormal a)
    lem-10 by-id by-id = refl
    lem-10 {A} {k} (by-nothing e p) (by-nothing .e q) i = by-nothing e (isSet-Str {!!}  p q i) -- (hlevel {{ISet:this {{of ⟨ T ⟩ A}}}})
    lem-10 (by-later p e x) (by-later .p .e y) i = by-later p e (lem-10 x y i)

    instance
      IProp:isNormal : ∀{A : IdxSet K 𝑖} {k} {a : ⟨ Mod A k ⟩} -> IHType 1 (isNormal a)
      IHType.hlevel IProp:isNormal = lem-10


  Mod-Normal : IdxSet K 𝑖 -> K -> Set 𝑖
  ⟨ Mod-Normal X k ⟩ = ∑ λ (a : ⟨ Mod X k ⟩) -> isNormal a
  of Mod-Normal X k = {!!}


  private
    module _ {X : IdxSet K 𝑖} where


      ν-impl : {j k : K} -> (p : QPath {{of Q}} (k) (j)) -> ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod-Normal X k ⟩
      ν-impl (last e) x with split-+-Str (δ x e)
      ... | left (tt , z) = (_ , some (last e) , x) , by-nothing e z
      ... | just (x' , _) = (_ , id-Q , x') , by-id
      ν-impl (e ∷ p) x with ν-impl p x
      ... | (_ , some p' , x') , N = (_ , some (e ∷ p') , x') , by-later _ _ N
      ... | (_ , id-Q , x') , N with split-+-Str (δ x' e)
      ... | left (tt , z) = (_ , some (last e) , x') , by-nothing e z
      ... | just (x'' , _) = (_ , id-Q , x'') , by-id


      ν : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod-Normal X k ⟩
      ν {.j} (j , id-Q , x) = (_ , id-Q , x) , by-id
      ν {k} (j , some p , x) = ν-impl p x

      ν₁ : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod X k ⟩
      ν₁ x = fst (ν x)


      write : ∀{k j} -> (e : Edge {{of Q}} j k) -> ⟨ Mod X k ⟩ -> ⟨ Mod X j ⟩
      write e (_ , p , x) = (_ , ` e ` ◆ p , x)


      ν-idempotent-impl : ∀{k j} -> (p : QPath {{of Q}} j k) (x : ⟨ ⟨ T ⟩ X ⟩ k) -> isNormal (_ , some p , x) -> ν₁ (_ , some p , x) ≡-Str (_ , some p , x)
      ν-idempotent-impl .(last e) x (by-nothing e P) with split-+-Str (δ x e)
      ... | left _ = refl
      ... | just (_ , Q) = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      ν-idempotent-impl .(e ∷ p) x (by-later p e N) with ν-impl p x | ν-idempotent-impl p x N
      ... | .(_ , some p , x) , snd₁ | refl-StrId = refl

      ν-idempotent : ∀{k} -> ∀(a : ⟨ Mod-Normal X k ⟩) -> ν₁ (fst a) ≡-Str fst a
      ν-idempotent ((_ , (some p) , x) , N) = ν-idempotent-impl p x N
      ν-idempotent ((_ , .id-Q , x) , by-id) = refl



      write-comm-impl : {j k l : K} -> (e : Edge {{of Q}} l k) -> (p : QPath {{of Q}} k j) -> (x : ⟨ ⟨ T ⟩ X ⟩ j) -> ν₁ (write e (fst (ν-impl p x))) ≡-Str fst (ν-impl (e ∷ p) x)
      write-comm-impl f (last e) x with split-+-Str (δ x e)
      ... | just (x' , P) with split-+-Str (δ x' f)
      ... | left x₁ = refl
      ... | just x₁ = refl
      write-comm-impl f (last e) x | left (tt , P) with split-+-Str (δ x e)
      ... | left x₁ = refl
      ... | just (_ , Q) = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      write-comm-impl f (e ∷ p) x with ν-impl p x
      ... | (_ , some p' , x') , N = ν-idempotent-impl (f ∷ e ∷ p') x' (by-later _ _ (by-later _ _ N))
      ... | (_ , id-Q , x') , N with split-+-Str (δ x' e)
      ... | left (tt , P) with split-+-Str (δ x' e)
      ... | left _ = refl
      ... | just (_ , Q) = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      write-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | just (x'' , _) with split-+-Str (δ x'' f)
      ... | left _ = refl
      ... | just _ = refl




      write-comm : ∀{k j} -> (e : Edge {{of Q}} j k) -> (x : ⟨ Mod X k ⟩)-> ν₁ (write e (ν₁ x)) ≡ ν₁ (write e x)
      write-comm e (j , id-Q , x) = refl
      write-comm e (j , some p , x) = ` write-comm-impl e p x `

    module _ {X Y : IdxSet K 𝑖} where
      apply : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> ⟨ Mod X k ⟩ -> ⟨ Mod Y k ⟩
      apply f (_ , p , x) = (_ , p , ⟨ _=<< {{of T'}} f ⟩ x)


      -- δ-comm : ∀(f : X ⟶ ⟨ T ⟩ Y) -> ∀{j k} -> ∀(e : Edge {{of Q}} k j) (x : ⟨ ⟨ T ⟩ X ⟩ j) -> map-Maybe (⟨ map f ◆ join ⟩ {_}) (δ x e) ≡ δ (⟨ map f ◆ join ⟩ x) e
      -- δ-comm f {j} {k} e x i = naturalJoinCommute {T = T'} decompose f commutes:decompose {_} x i {_} e



      apply-comm-impl : {j k : K} -> (f : X ⟶ ⟨ T ⟩ Y) -> (p : QPath {{of Q}} k j) -> (x : ⟨ ⟨ T ⟩ X ⟩ j) -> ν₁ (apply f (fst (ν-impl p x))) ≡ fst (ν ((_ , some p , ⟨ map f ◆ join ⟩ {_} x)))
      apply-comm-impl f (last e) x with (δ-comm f e x) | split-+-Str (δ x e)
      ... | X | left x₁ = refl
      ... | X | just (a , P) with split-+-Str (δ (⟨ map f ◆ join ⟩ {_} x) e)
      ... | left (tt , Q) =
        let R : map-Maybe (⟨ map f ◆ join ⟩ {_}) (just a) ≡ nothing
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ {_})) (≡-Str→≡ (P ⁻¹)) ∙ X (λ P' -> right≢left (` P ⁻¹ ` ∙ P')) ∙ ` Q `
        in 𝟘-rec (right≢left R)
      ... | just (b , Q) =
        let R : map-Maybe (⟨ map f ◆ join ⟩ {_}) (just a) ≡ just b
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ {_})) (≡-Str→≡ (P ⁻¹)) ∙ X (λ P' -> right≢left (` P ⁻¹ ` ∙ P')) ∙ ` Q `

        in λ i -> (_ , id-Q , isInjective:right R i)

      -- see 2021-02-20:
      apply-comm-impl f (e ∷ p) x with ν-impl p x | ν-impl p (⟨ map f ◆ join ⟩ {_} x) | ≡→≡-Str (apply-comm-impl f p x)
      ... | (_ , some p' , x') , N    | (_ , p'2 , x'2) , N2 | Y with ν-impl p' (⟨ map f ◆ join ⟩ {_} x')
      apply-comm-impl f (e ∷ p) x | (_ , some p' , x') , N | (_ , id-Q , x'2) , N2 | refl-StrId | .(_ , id-Q , x'2) , snd₁ = refl
      apply-comm-impl f (e ∷ p) x | (_ , some p' , x') , N | (_ , some x₁ , x'2) , N2 | refl-StrId | .(_ , some x₁ , x'2) , snd₁ = refl

      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(fst (ν (_ , id-Q , _))) , snd₁ | refl-StrId with split-+-Str (δ x' e) | split-+-Str (δ (⟨ map f ◆ join ⟩ {_} x') e)
      ... | just (a , P) | left (tt , Q) =
        -- NOTE: here we do the same as in the `last e` case above
        let R : map-Maybe (⟨ map f ◆ join ⟩ {_}) (just a) ≡ nothing
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ {_})) (≡-Str→≡ (P ⁻¹)) ∙ δ-comm f e x' (λ P' -> right≢left (` P ⁻¹ ` ∙ P')) ∙ ` Q `
        in 𝟘-rec (right≢left R)
        -- NOTE: here we do the same as in the `last e` case above
      ... | just (a , P) | just (b , Q) =
        let R : map-Maybe (⟨ map f ◆ join ⟩ {_}) (just a) ≡ just b
            R = cong (map-Maybe (⟨ map f ◆ join ⟩ {_})) (≡-Str→≡ (P ⁻¹)) ∙ δ-comm f e x' (λ P' -> right≢left (` P ⁻¹ ` ∙ P')) ∙ ` Q `
        in λ i -> (_ , id-Q , isInjective:right R i)

      ... | left (tt , Q) | Z with split-+-Str (δ (⟨ map f ◆ join ⟩ {_} x') e)
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | just (_ , Z1) | left (_ , Z2) = 𝟘-rec (left≢right `(Z2 ⁻¹ ∙ Z1)`)
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | just (_ , Z1) | just (_ , Z2) = λ i -> (_ , id-Q , isInjective:right R i)
        where R = `(Z2 ⁻¹ ∙ Z1)`
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | left x₁ | left x₂ = refl
      apply-comm-impl f (e ∷ p) x | (_ , id-Q , x') , N | .(_) , snd₁ | refl-StrId | left (tt , Q) | left (_ , Z1) | just (_ , Z2) = 𝟘-rec (right≢left `(Z2 ⁻¹ ∙ Z1)`)


-- ... | (_ , some p' , x') , N    | (_ , id-Q , x'2) , N2 | Y  = {!!}
      -- ... | (_ , some p' , x') , N    | (_ , some p'2 , x'2) , N2 | Y with ν-impl p' (⟨ map f ◆ join ⟩ {_} x')
      -- apply-comm-impl f (e ∷ p) x | (_ , some p' , x') , N | (_ , some p'2 , x'2) , N2 | refl-StrId | .(_ , some p'2 , x'2) , snd₁ = refl


      apply-comm : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> (x : ⟨ Mod X k ⟩) -> ν₁ (apply f (ν₁ x)) ≡ ν₁ (apply f x)
      apply-comm f (_ , id-Q , x) = refl
      apply-comm f (_ , some p , x) = apply-comm-impl f p x
      -- apply-comm f (_ , id-Q , x) = refl
      -- apply-comm f (_ , some x₁ , x) = {!!}

  𝑺 : IdxSet K 𝑖 -> PSh 𝔇 𝑖
  𝑺 X = mirror-Functor (free-Diagram f)
    where f : QuiverHom (Q) (ForgetCategory (` Set 𝑖 ` ᵒᵖ))
          ⟨ f ⟩ k = Mod-Normal X k
          ⟨ IQuiverHom.qmap (of f) e ⟩ (x , _) = ν (write e x)
          of IQuiverHom.qmap (of f) e = record {}


  private
    module _ {X Y : IdxSet K 𝑖} (f : X ⟶ ⟨ T ⟩ Y) where

  {-
      g' : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod Y k ⟩
      g' ((j , p , left a)) = ((j , p , left a)) -- normaliz
      g' ((j , p , just x)) = (j , p , just (⟨ f =<< ⟩ j x))
      -}

      g : ∀(k : K) -> ⟨ 𝑺 X ⟩ k ⟶ ⟨ 𝑺 Y ⟩ k
      ⟨ g k ⟩ (x , xp) = ν (apply f x)


      gp : {a b : K} (e : (Edge {{Dir}} b a)) (x : ⟨ ⟨ 𝑺 X ⟩ a ⟩) →
            ⟨ map {{of 𝑺 Y}} (⩚ e) ⟩ (⟨ g a ⟩ x) ≡
            ⟨ g b ⟩ (⟨ map {{of 𝑺 X}} (⩚ e) ⟩ x)
      gp e ((j , p , x) , pp) = byFirstP P

       where P : ν₁ (write e (ν₁ (apply f (j , p , x))))
                  ≡
                ν₁ (apply f (ν₁ (write e (j , p , x))))
             P = write-comm e (apply f (j , p , x)) ∙ apply-comm f (write e (j , p , x)) ⁻¹

  module _ {X Y : IdxSet K 𝑖} where
    map-𝑺 : (f : X ⟶ ⟨ T ⟩ Y) -> 𝑺 X ⟶ 𝑺 Y
    map-𝑺 f = mirror-Nat (free-Diagram-Natimpl (g f) (λ e x -> gp f e x ⁻¹))

  private
    module _ {X : IdxSet K 𝑖} where
      ι : ∀{k} -> (x : ⟨ ⟨ T ⟩ X ⟩ k) -> ⟨ Mod-Normal X k ⟩
      ι x = (_ , id-Q , x) , by-id

      infixr 40 _↷_
      _↷_ : ∀{k j} -> Hom {{of 𝔇}} j k -> (x : ⟨ Mod-Normal X k ⟩) -> ⟨ Mod-Normal X j ⟩
      _↷_ f x = ⟨ map {{of 𝑺 X}} f ⟩ x

      assoc-↷ : ∀{j k l} -> {f : Hom {{of 𝔇}} l k} -> {g : Hom {{of 𝔇}} k j} -> {x : ⟨ Mod-Normal X j ⟩}
                -> f ↷ g ↷ x ≡ (f ◆ g) ↷ x
      assoc-↷ {f = f} {g = g} {x} = functoriality-◆ {{of 𝑺 X}} {f = g} {g = f} x ⁻¹

      mModNormal : ∀ k j p x -> ⟨ Mod X k ⟩
      mModNormal k j p x = (j , p , x)

      QPath-break : ∀{k l1 l2 j} -> {e : Edge {{of Q}} k l1} {f : Edge {{of Q}} k l2} {p : QPath {{of Q}} l1 j} {q : QPath {{of Q}} l2 j} -> _≡-Str_ {A = QPath k j} (e ∷ p) (f ∷ q) -> (QQ : l1 ≡ l2)
                  -> transport (λ i -> QPath {{of Q}} (QQ i) j) p ≡ q
      QPath-break {l1 = l1} {l2} {j} {e} {f} {p} {q} refl-StrId QQ = X3
        where X1 : refl ≡ QQ
              X1 = hlevel {{ISet:K}} l1 l1 refl QQ
              X2 : transport (λ i -> QPath {{of Q}} l1 j) p ≡ p
              X2 = transportRefl p
              X3 : transport (λ i -> QPath {{of Q}} (QQ i) j) p ≡ p
              X3 = transport (λ k -> transport (λ i -> QPath {{of Q}} (X1 k i) j) p ≡ p) X2


      lem-000 : ∀{k} -> ∀ j1 j2 -> ∀ (e1 : Edge {{Dir}} k k) (e2 : Edge {{Dir}} k k) -> (p1 : QPath {{of Q}} k j1) (p2 : QPath {{of Q}} k j2)
                -> (p : j1 ≡ j2) -> PathP (λ i -> QPath₊ k (p i)) (some (e1 ∷ p1)) (some (e2 ∷ p2)) -> PathP (λ i -> QPath k (p i)) p1 p2
      lem-000 {k} j1 j2 e1 e2 p1 p2 p q with ≡→≡-Str p
      ... | refl-StrId = q5
        where
            P1 : p ≡ refl
            P1 = hlevel {{ISet:K}} _ _ p refl

            P0 : Path (QPath₊ k j1) (some (e1 ∷ p1)) (some (e2 ∷ p2))
            P0 = transport (λ α -> PathP (λ i → QPath₊ k (P1 α i)) (some (e1 ∷ p1)) (some (e2 ∷ p2))) q

            f : (pp : QPath₊ {{of Q}} k j1) -> QPath {{of Q}} k j1
            f id-Q = last a0
            f (some x) = x

            q2 : PathP (λ i -> QPath k j1) ((e1 ∷ p1)) ((e2 ∷ p2))
            q2 i = f (P0 i)

            q3 : PathP (λ i -> QPath k j1) (transport (λ i -> QPath {{of Q}} k j1) p1) (p2)
            q3 = QPath-break (≡→≡-Str q2) refl

            q4 : PathP (λ i -> QPath k j1) (p1) (p2)
            q4 = transport (λ α -> PathP (λ i -> QPath k j1) (transportRefl p1 α) (p2)) q3

            q5 : PathP (λ i -> QPath k (p i)) (p1) (p2)
            q5 = transport (λ α -> PathP (λ i -> QPath k (P1 (~ α) i)) p1 p2) q4


      lem-00 : ∀ {k} -> ∀ j1 j2 -> ∀ x1 x2 -> ∀ (e1 : Edge {{Dir}} k k) (e2 : Edge {{Dir}} k k) -> (p1 : QPath {{of Q}} k j1) (p2 : QPath {{of Q}} k j2)
               -> mModNormal k j1 (some (e1 ∷ p1)) x1 ≡ mModNormal k j2 (some (e2 ∷ p2)) x2
               -> mModNormal k j1 (some p1) x1 ≡ mModNormal k j2 (some p2) x2
      lem-00 _ _ _ _ _ _ _ _ p = λ i -> p i .fst , some (lem-000 _ _ _ _ _ _ (λ i -> p i .fst) (λ i -> p i .snd .fst) i) , (p i .snd .snd)

      -- cancel-↷-impl-2 : ∀{k} -> (x y : ⟨ ⟨ T ⟩ X ⟩ k) -> (∀{j} -> (e : Edge {{Dir}} j k) -> ` e ` ↷ ι x ≡ ` e ` ↷ ι y) -> x ≡ y
      -- cancel-↷-impl-2 x y P with decideDecompose x | decideDecompose y
      -- cancel-↷-impl-2 {k} x y P | left (Px , _) | left (Py , _) with split-+-Str (δ x a1) | split-+-Str (δ y a1) | (P a1) | ≡→≡-Str (P a1)
      -- ... | left x₁ | left x₂ | XX | _ =
      --   let ρ : k ≡ k
      --       ρ = λ i -> XX i .fst .fst
      --       ρ-refl : ρ ≡ refl
      --       ρ-refl = hlevel {{ISet:K}} _ _ ρ refl
      --       P : PathP (λ i -> ⟨ ⟨ T ⟩ X ⟩ (ρ i)) x y
      --       P i = XX i .fst .snd .snd
      --   in transport (λ α -> PathP (λ i -> ⟨ ⟨ T ⟩ X ⟩ (ρ-refl α i)) x y) P
      -- ... | left (_ , R) | just (_ , S) | _ | ()
      -- ... | just (_ , R) | just x₂ | XX | _ = 𝟘-rec (right≢left (` R ⁻¹ ∙ Px `))
      -- cancel-↷-impl-2 x y P | left (Px , _) | just Dy       = {!!} -- 𝟘-rec (right≢left (` Dy a1 .snd ⁻¹ ∙ Px `))
      -- cancel-↷-impl-2 x y P | just Dx       | left (Py , _) = {!!}
      -- cancel-↷-impl-2 x y P | just Dx       | just Dy       = {!!}

      δ-decomp : ∀{k j} -> (e : Edge {{of Q}} k j) -> (x : ⟨ ⟨ T ⟩ X ⟩ j) -> (Dx : isDecomposable x) -> ` e ` ↷ ι x ≡ ι (Dx e .fst)
      δ-decomp e x Dx with split-+-Str (δ x e)
      ... | left (_ , R) = 𝟘-rec (right≢left (` Dx e .snd ⁻¹ ∙ R `))
      ... | just (a , S) with Dx e .snd ⁻¹ ∙ S
      ... | refl-StrId = refl

      injective-ι : ∀{k j} -> {p q : QPath₊ {{of Q}} j k} {x y : ⟨ ⟨ T ⟩ X ⟩ k} -> {N : isNormal (_ , p , x)} {M : isNormal (_ , q , y)} -> Path (⟨ Mod-Normal X j ⟩) ((k , p , x) , N) ((k , q , y) , M) -> x ≡ y
      injective-ι {k} {x = x} {y = y} XX = P1
        where ρ : k ≡ k
              ρ = λ i -> XX i .fst .fst
              ρ-refl : ρ ≡ refl
              ρ-refl = hlevel {{ISet:K}} _ _ ρ refl
              P0 : PathP (λ i -> ⟨ ⟨ T ⟩ X ⟩ (ρ i)) x y
              P0 i = XX i .fst .snd .snd
              P1 : PathP (λ i -> ⟨ ⟨ T ⟩ X ⟩ k) x y
              P1 = transport (λ α -> PathP (λ i -> ⟨ ⟨ T ⟩ X ⟩ (ρ-refl α i)) x y) P0

      cancel-↷-impl-2 : ∀{k} -> (x y : ⟨ ⟨ T ⟩ X ⟩ k) -> (∀{j} -> (e : Edge {{Dir}} j k) -> ` e ` ↷ ι x ≡ ` e ` ↷ ι y) -> x ≡ y
      cancel-↷-impl-2 {k} x y P with split-+-Str (δ x a1) | split-+-Str (δ y a1) | (P a1) | ≡→≡-Str (P a1)
      ... | left x₁ | left x₂ | XX | _ = injective-ι XX
      ... | just (a , R) | just (b , S) | XX | _ with decideDecompose x | decideDecompose y
      ... | left (Px) | just Dy = let Px = makePure Px .fst; Dy = makeDec Dy       in 𝟘-rec (left≢right (` Px ⁻¹ ∙ R ` ∙ cong (right {A = 𝟙-𝒰}) (injective-ι XX)  ∙ ` S ⁻¹ ∙ Dy a1 .snd `)) 
      ... | just Dx   | left Py = let Py = makePure Py .fst; Dx = makeDec Dx       in 𝟘-rec (left≢right (` Py ⁻¹ ∙ S ` ∙ cong (right {A = 𝟙-𝒰}) (injective-ι XX) ⁻¹  ∙ ` R ⁻¹ ∙ Dx a1 .snd `))
      ... | left Px   | left Py = let Px = makePure Px .fst; Py = makePure Py .fst in 𝟘-rec (left≢right (` Px ⁻¹ ∙ R `))
      ... | just Dx   | just Dy = let Dx' = makeDec Dx      ; Dy' = makeDec Dy       in cancel-δ x y Dx Dy (λ e -> ` Dx' e .snd ` ∙ cong (right {A = 𝟙-𝒰}) (injective-ι (δ-decomp e x Dx' ⁻¹ ∙ P e ∙ δ-decomp e y Dy')) ∙ ` Dy' e .snd ⁻¹ `)


      cancel-↷-impl : ∀{k} -> (x y : ⟨ Mod-Normal X k ⟩) -> (∀{j} -> ∀(e : Edge {{Dir}} j k) -> ` e ` ↷ x ≡ ` e ` ↷ y) -> fst x ≡ fst y
      cancel-↷-impl ((_ , p , x) , N) ((_ , q , y) , M) P with (P a0)
      cancel-↷-impl ((_ , id-Q , x) , N) ((_ , id-Q , y) , M) P | X = λ i -> (_ , id-Q , cancel-↷-impl-2 x y P i)
      cancel-↷-impl ((_ , id-Q , x) , N) ((_ , some q , y) , M) P | X with ν-impl q y | ν-idempotent-impl q y M | split-+-Str (δ x a0) | ≡→≡-Str X
      ... | .(_ , some q , y) , snd₁ | refl-StrId | left x₁ | ()
      ... | .(_ , some q , y) , snd₁ | refl-StrId | just x₁ | ()
      cancel-↷-impl ((_ , some p , x) , N) ((_ , id-Q , y) , M) P | X with ν-impl p x | ν-idempotent-impl p x N | split-+-Str (δ y a0) | ≡→≡-Str X
      ... | .(_ , some p , x) , snd₁ | refl-StrId | left x₁ | ()
      ... | .(_ , some p , x) , snd₁ | refl-StrId | just x₁ | ()
      cancel-↷-impl ((k , some p , x) , N) ((_ , some q , y) , M) P | X with ν-impl p x | ν-impl q y | ν-idempotent-impl p x N | ν-idempotent-impl q y M
      ... | .(_ , some p , x) , snd₁ | .(_ , some q , y) , snd₂ | refl-StrId | refl-StrId = lem-00 _ _ _ _ _ _ _ _ (cong fst X)

      cancel-↷ : ∀{k} -> (x y : ⟨ Mod-Normal X k ⟩) -> (∀{j} -> ∀(e : Edge {{Dir}} j k) -> ` e ` ↷ x ≡ ` e ` ↷ y) -> x ≡ y
      cancel-↷ x y P = byFirstP (cancel-↷-impl x y P)

      -- with ≡→≡-Str (λ i -> X i .fst .fst)
      -- ... | refl-StrId = λ i -> (k , some (F a1 a1 p q (λ i -> X i .fst .snd .fst)) , ?) , ?
      --   where F : ∀{l k j} -> (e1 e2 : Edge {{of Q}} l k) -> (p1 p2 : QPath {{of Q}} k j) -> (Path (QPath₊ l j) (some (e1 ∷ p1)) (some (e2 ∷ p2))) -> p1 ≡ p2
      --         F = {!!}

      -- cong-Str (λ ξ -> F ξ .snd) X
        -- where F : ∀{k A} -> ⟨ Mod-Normal A k ⟩ -> ∑ λ j -> ⟨ Mod-Normal A j ⟩
        --       F ((j , id-Q , x) , N) = {!!}
        --       F ((j , some (last x₁) , x) , N) = {!!}
        --       F ((j , some (x₁ ∷ p) , x) , by-later .p .x₁ N) = _ , ((_ , some p , x) , N)


        -- where P : ∀{k1 k2 j1 j2 i1 i2} -> (p : )

-- with cong-Str (λ ξ -> fst (fst ξ)) X
--       ... | refl-StrId with cong-Str (λ ξ -> (fst ξ)) X
--       ... | X' = {!!}

      lem-0 : ∀{k} -> (x : ⟨ ⟨ T ⟩ X ⟩ k) -> ` a0 ` ↷ ι x ≡ ι e0
      lem-0 {k = k} x with split-+-Str (δ x a0) | ≡→≡-Str (a0-adsorb x)
      ... | left (_ , P) | Q = 𝟘-rec (left≢right `(P ⁻¹ ∙ Q)`)
      ... | just (b , P) | Q with P ⁻¹ ∙ Q
      ... | refl-StrId = refl

      module lem-01 {k} (x : ⟨ ⟨ T ⟩ X ⟩ k) where
        proof : ∀ {j} -> (p : Hom {{of 𝔇}} j k) -> (N : isNormal (k , p , x)) -> p ↷ ((k , id-Q , x) , by-id) ≡ ((k , p , x) , N)

        P1 : ∀ {j l} -> (e : Edge {{of Q}} l j) -> (p : QPath {{of Q}} j k) -> (N : isNormal (k , ` p ` , x)) -> (` e ` ↷ ((k , ` p ` , x) , N)) ≡ ((k , ` e ` ◆ ` p ` , x) , by-later _ _ N)
        P1 e p N with ν-impl p x | ν-idempotent-impl p x N
        ... | .(k , some p , x) , snd₁ | refl-StrId = byFirstP refl

        P0 : ∀ {j} -> (p : QPath {{of Q}} j k) -> (N : isNormal (k , ` p ` , x)) -> (` p ` ↷ ((k , id-Q , x) , by-id)) ≡ ((k , ` p ` , x) , N)
        P0 (last e) N with split-+-Str (δ x e)
        P0 (last e) (by-nothing .e x₁) | left x = byFirstP refl
        P0 (last e) (by-nothing .e P) | just (_ , Q) = 𝟘-rec (left≢right (` P ⁻¹ ∙ Q `))
        P0 (e ∷ p) (by-later .p .e N) =
          -- let Q : (` e ∷ p ` ↷ ((k , id-Q , x) , by-id)) ≡ (k , ` e ∷ p ` , x)
          let Q = (some (e ∷ p) ↷ ((k , id-Q , x) , by-id)) ≡⟨ assoc-↷ {f = ` e `} {g = ` p `} {x = ((k , id-Q , x) , by-id)} ⁻¹ ⟩
                  (` e ` ↷ ` p ` ↷ ((k , id-Q , x) , by-id)) ≡[ i ]⟨ ` e ` ↷ P0 p N i ⟩
                  (` e ` ↷ ((k , ` p ` , x) , N))           ≡⟨ (P1 e p N) ⟩
                  ((k , some (e ∷ p) , x) , by-later p e N)     ∎
          in Q

        proof id-Q by-id = refl
        proof (some p) = P0 p

      module lem-02 {k} (x : ⟨ ⟨ T ⟩ X ⟩ k) (x≢e0 : x ≢-Str e0) {j} (e : Edge {{of Q}} j k) (D : isDecomposable x) where
        proof : ∑ λ y -> (` e ` ↷ ι x ≡ ι y) ×-𝒰 ((_ , y) ≺ (_ , x))
        proof with split-+-Str (δ x e) | D e
        ... | left (a , P) | y , Q = 𝟘-rec (right≢left `(Q ⁻¹ ∙ P)`)
        ... | just (a , P) | y , Q with P ⁻¹ ∙ Q
        ... | refl-StrId = y , refl , (x≢e0 , (e , P))



    module _ {X Y : IdxSet K 𝑖} (α : 𝑺 X ⟶ 𝑺 Y) where
      -- lem-1 : ∀{k : K} -> {} -> ⟨ ⟨ α ⟩ ⟩ (ι {k = k} e0) ≡ ι e0


      module lem-1 {k : K} (x : ⟨ ⟨ T ⟩ X ⟩ k) where
        α' = ⟨ ⟨ α ⟩ {k} ⟩
        P1 : ∀ y -> ` a0 ` ↷ α' (ι y) ≡ α' (ι e0)
        P1 = λ y -> ` a0 ` ↷ α' (ι y) ≡⟨ naturality {{of α}} ` a0 ` (ι y) ⟩
                    α' (` a0 ` ↷ ι y) ≡[ i ]⟨ α' (lem-0 y i) ⟩
                    α' (ι e0)          ∎

        P1-1 : ` a0 ` ↷ α' (ι x) ≡ α' (ι e0)
        P1-1 = P1 x

        P1-2 : (` a0 ` ◆ ` a0 `) ↷ α' (ι x) ≡ α' (ι e0)
        P1-2 = (` a0 ` ◆ ` a0 `) ↷ α' (ι x) ≡⟨ assoc-↷ {f = ` a0 `} {g = ` a0 `} {x = α' (ι x)} ⟩
                ` a0 ` ↷ (` a0 ` ↷ α' (ι x)) ≡[ i ]⟨ ` a0 ` ↷ P1 x i ⟩
                ` a0 ` ↷ α' (ι e0)          ≡⟨ P1 e0 ⟩
                α' (ι e0)                    ∎

        P2 : ` a0 ` ↷ α' (ι x) ≡ (` a0 ` ◆ ` a0 `) ↷ α' (ι x)
        P2 = P1-1 ∙ P1-2 ⁻¹

        proof : ∑ λ y -> ⟨ ⟨ α ⟩ ⟩ (ι x) ≡ ι y
        proof with α' (ι x) | ≡→≡-Str P2
        ... | (_ , id-Q , x') , by-id | _ = _ , refl
        ... | (_ , some p' , x') , N   | Q with ν-impl p' x' | ν-idempotent-impl p' x' N
        ... | .(_ , some p' , x') , N2 | refl-StrId with ν-impl p' x' | ν-idempotent-impl p' x' N2
        proof | (_ , some p' , x') , N | () | .(_ , some p' , x') , N2 | refl-StrId | .(_ , some p' , x') , snd₁ | refl-StrId

      module lem-15 {k : K} where
        α' = ⟨ ⟨ α ⟩ {k} ⟩
        proof : α' (ι e0) ≡ ι e0
        proof = α' (ι e0) ≡[ i ]⟨ α' ((lem-0 e0 ⁻¹) i) ⟩
                α' (` a0 ` ↷ ι e0) ≡⟨ naturality {{of α}} ` a0 ` (ι e0) ⁻¹ ⟩
                ` a0 ` ↷ α' (ι e0) ≡[ i ]⟨ ` a0 ` ↷ lem-1.proof e0 .snd i ⟩
                ` a0 ` ↷ (ι _)     ≡⟨ lem-0 _ ⟩
                ι e0 ∎


  module _ {X Y : IdxSet K 𝑖} where
    map⁻¹-𝑺 : (𝑺 X ⟶ 𝑺 Y) -> (X ⟶ ⟨ T ⟩ Y)
    ⟨ map⁻¹-𝑺 α ⟩ x = lem-1.proof α (⟨ return ⟩ {_} x) .fst

    module lem-2 (f : X ⟶ ⟨ T ⟩ Y) where
      proof : map⁻¹-𝑺 (map-𝑺 f) ≣ f

      -- | It is enough to show that:
      P0 : ∀ {k} (x : ⟨ X ⟩ k) → ⟨ return ◆ map f ◆ join ⟩ {k} x ≡ ⟨ f ⟩ {k} x
      P0 {k} x = ⟨ return ◆ map f ◆ join ⟩ {k} x ≡[ i ]⟨  ⟨ join ⟩ (naturality f {k} x i) ⟩
               ⟨ f ◆ return ◆ join ⟩ {k} x     ≡⟨ unit-l-join (⟨ f ⟩ {k} x) ⟩
               ⟨ f ⟩ {k} x                     ∎

      proof = P0

    module lem-3 (α : 𝑺 X ⟶ 𝑺 Y) where
      proof : map-𝑺 (map⁻¹-𝑺 α) ≣ α

      -- | We set [..].
      β = map-𝑺 (map⁻¹-𝑺 α)
      Ξ = ∑ λ k -> ⟨ ⟨ T ⟩ X ⟩ k
      η' : ∀{k} -> ∀{A : IdxSet K 𝑖} -> ⟨ A ⟩ k -> ⟨ ⟨ T ⟩ A ⟩ k
      η' = ⟨ return ⟩ {_}

      μ' : ∀{k} -> ∀{A : IdxSet K 𝑖} -> ⟨ ⟨ T ◆ T ⟩ A ⟩ k -> ⟨ ⟨ T ⟩ A ⟩ k
      μ' = ⟨ join ⟩ {_}


      -- | We want to show:
      𝑃 : Ξ -> 𝒰 _
      𝑃 (k , x) = ⟨ ⟨ β ⟩ ⟩ (ι x) ≡ ⟨ ⟨ α ⟩ ⟩ (ι x)

      -- | We do this with an induction, the base case is:
      P3-base : ∀ {k} -> (x : ⟨ X ⟩ k) -> 𝑃 (k , η' x)
      P3-base x = byFirstP P0
        where P0 = (_ , id-Q , μ' (⟨ map (map⁻¹-𝑺 α) ⟩ {_} (η' x))) ≡[ i ]⟨ _ , id-Q , μ' (naturality (map⁻¹-𝑺 α) {_} x i) ⟩
                   (_ , id-Q , μ' ( η' (⟨ map⁻¹-𝑺 α ⟩ {_} x)))      ≡[ i ]⟨ _ , id-Q , unit-l-join (⟨ map⁻¹-𝑺 α ⟩ {_} x) i ⟩
                   (_ , id-Q , (⟨ map⁻¹-𝑺 α ⟩ {_} x))               ≡⟨ refl ⟩
                   (_ , id-Q , (lem-1.proof α (η' x) .fst))       ≡[ i ]⟨ lem-1.proof α (η' x) .snd (~ i) .fst ⟩
                   fst (⟨ ⟨ α ⟩ ⟩ (ι (η' x)))                      ∎

      P3-step : ∀ (x : Ξ) -> (x .snd ≢-Str e0) -> (isDecomposable (snd x)) -> (∀ y -> y ≺ x -> 𝑃 y) -> 𝑃 x
      P3-step (k , x) x≢e0 D Hyp = cancel-↷ (⟨ ⟨ β ⟩ ⟩ (ι x)) (⟨ ⟨ α ⟩ ⟩ (ι x)) P0
        where P0 : ∀{j} -> (e : Edge {{of Q}} j k) -> ` e ` ↷ ⟨ ⟨ β ⟩ ⟩ (ι x) ≡ ` e ` ↷ ⟨ ⟨ α ⟩ ⟩ (ι x)
              P0 e = ` e ` ↷ ⟨ ⟨ β ⟩ ⟩ (ι x) ≡⟨ naturality {{of β}} ` e ` (ι x) ⟩
                     ⟨ ⟨ β ⟩ ⟩ (` e ` ↷ ι x) ≡[ i ]⟨ ⟨ ⟨ β ⟩ ⟩  (lem-02.proof x x≢e0 e D .snd .fst i) ⟩
                     ⟨ ⟨ β ⟩ ⟩ (ι _)          ≡⟨ Hyp _          (lem-02.proof x x≢e0 e D .snd .snd) ⟩
                     ⟨ ⟨ α ⟩ ⟩ (ι _)          ≡[ i ]⟨ ⟨ ⟨ α ⟩ ⟩ (lem-02.proof x x≢e0 e D .snd .fst (~ i)) ⟩
                     ⟨ ⟨ α ⟩ ⟩ (` e ` ↷ ι x) ≡⟨ naturality {{of α}} ` e ` (ι x) ⁻¹ ⟩
                     ` e ` ↷ ⟨ ⟨ α ⟩ ⟩ (ι x) ∎


      P3 : ∀ x -> (∀ y -> y ≺ x -> 𝑃 y) -> 𝑃 x
      P3 (k , x) Q with decideDecompose x
      ... | (right D) with decide-e0 x
      ... | yes refl-StrId = lem-15.proof β ∙ lem-15.proof α ⁻¹
      ... | no ¬p = P3-step (k , x) ¬p (makeDec D) Q
      P3 (k , x) Q | (left Px) with makePure Px
      ... | (_ , (x' , refl-StrId)) = P3-base x'

      P3' : ∀ x -> (∀ y -> y ≺P x -> 𝑃 y) -> 𝑃 x
      P3' x P = P3 x (λ y y≺x -> P y (recreate-≺ y≺x))


      -- | Now we use well foundedness to conclude that the statement holds for all |x|.
      P2 : (k : K) (x : ⟨ ⟨ T ⟩ X ⟩ k) -> ⟨ ⟨ map-𝑺 (map⁻¹-𝑺 α) ⟩ ⟩ (ι x) ≡ ⟨ ⟨ α ⟩ ⟩ (ι x)
      P2 k x = WFI.induction isWellfounded::≺P {P = 𝑃} P3' (k , x)


      P1 : (k : K) (j : K) -> (p : Hom {{of 𝔇}} k j) -> (x : ⟨ ⟨ T ⟩ X ⟩ j) -> (N : isNormal (j , p , x)) ->

              ⟨ ⟨ β ⟩ ⟩ ((j , p , x) , N) ≡ ⟨ ⟨ α ⟩ ⟩ ((j , p , x) , N)

      P1 k j p x N = ⟨ ⟨ β ⟩ ⟩ ((j , p , x) , N)               ≡[ i ]⟨ ⟨ ⟨ β ⟩ ⟩ (lem-01.proof x p N (~ i)) ⟩
                     ⟨ ⟨ β ⟩ ⟩ (p ↷ ((j , id-Q , x) , by-id)) ≡⟨ naturality {{of β}} p _ ⁻¹ ⟩
                     p ↷ ⟨ ⟨ β ⟩ ⟩ (((j , id-Q , x) , by-id)) ≡[ i ]⟨ p ↷ P2 j x i ⟩
                     p ↷ ⟨ ⟨ α ⟩ ⟩ (((j , id-Q , x) , by-id)) ≡⟨ naturality {{of α}} p _ ⟩
                     ⟨ ⟨ α ⟩ ⟩ (p ↷ ((j , id-Q , x) , by-id)) ≡[ i ]⟨ ⟨ ⟨ α ⟩ ⟩ (lem-01.proof x p N i) ⟩
                     ⟨ ⟨ α ⟩ ⟩ ((j , p , x) , N) ∎

      proof k ((j , p , x) , N) = P1 k j p x N



    -- with ⟨ ⟨ f ⟩ ⟩ (ι (⟨ return ⟩ _ x))
    -- ... | a = {!!}

      -- ((_ , id-Q , ⟨ return {{of T'}} ⟩ _ x) , by-id)

    -- ⟨ map⁻¹-𝑺 f ⟩ k x with ⟨ ⟨ f ⟩ ⟩ ((_ , id , right (⟨ return ⟩ _ x)) , by-[])
    -- ... | (_ , q , left y) , _ = {!!}
    -- ... | (_ , id-Q , just y) , _ = y
    -- ... | (_ , some x₁ , just y) , _ = {!!}
    -- of map⁻¹-𝑺 f = record {}
    -- -- (free-Diagram-Natimpl (g f) (λ e x -> gp f e x))

{-



      -- where g : ∀(k : K) -> ⟨ 𝑺 X ⟩ k ⟶ ⟨ 𝑺 Y ⟩ k
      --       ⟨ g k ⟩ ((j , p , left a) , _) = ν ((j , p , left a)) -- ν (j , p , {!!}) -- (j , p ,  ⟨ f =<< ⟩ j x)
      --       ⟨ g k ⟩ ((j , p , just x) , _) = ν (j , p , just (⟨ f =<< ⟩ j x)) -- (j , p ,  ⟨ f =<< ⟩ j x)
      --       of g k = record {}

      --       gp : {a b : K} (e : Maybe (Edge {{Dir}} a b)) (x : ⟨ ⟨ 𝑺 X ⟩ a ⟩) →
      --             ⟨ map {{of 𝑺 Y}} (⩚ e) ⟩ (⟨ g a ⟩ x) ≡
      --             ⟨ g b ⟩ (⟨ map {{of 𝑺 X}} (⩚ e) ⟩ x)
      --       gp e ((j , p , left x) , _) = {!!}
      --       gp e ((j , p , just x) , _) = {!!}


            -- gp2 : {a b : K}
            --         (e : 𝟙-𝒰 +-𝒰 Edge {{Dir}} a b)
            --         (x
            --         : Σ (Σ K (λ j → Σ (Hom {{of 𝔇 ᵒᵖ}} j a) (λ a₁ → 𝟙-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j)))
            --           (isNormal X a)) →
            --         ν
            --         (fst (fst (⟨ g a ⟩ x)) ,
            --         (some (last e)) ◆ (fst (snd (fst (⟨ g a ⟩ x)))) ,
            --         snd (snd (fst (⟨ g a ⟩ x))))
            --         ≡
            --         ⟨ g b ⟩
            --         (ν
            --         (fst (fst x) ,
            --           (some (last e)) ◆ (fst (snd (fst x)))  ,
            --           snd (snd (fst x))))
            -- gp2 = {!!}
    -- ⟨ ⟨ map-𝑺 f ⟩ {x = k} ⟩ ((j , p , x) , _) = ν (j , p ,  ⟨ f =<< ⟩ j x)
    -- of ⟨ map-𝑺 f ⟩ = record {}
    -- INatural.naturality (of map-𝑺 f) = {!!}

-}


  Functor:𝑺 : Functor (` IdxSet K 𝑖 ` ⌄ T') `(PSh 𝔇 𝑖)`
  ⟨ Functor:𝑺 ⟩ X = 𝑺 ⟨ X ⟩
  IFunctor.map (of Functor:𝑺) f = map-𝑺 ⟨ f ⟩
  IFunctor.functoriality-id (of Functor:𝑺) = {!!}
  IFunctor.functoriality-◆ (of Functor:𝑺) = {!!}
  IFunctor.functoriality-≣ (of Functor:𝑺) = {!!}



{-
  𝔇 = Monoid:Free Dir

  private
    Mon : ∀(A : 𝒰 𝑖) -> MonoidModule 𝔇 𝑖
    Mon A = MonoidModule:Free 𝔇 (⟨ T ⟩ A)

  norm' : ⟨ 𝔇 ⟩ -> ⟨ T ⟩ A -> ⟨ Mon A ⟩
  norm' [] a = ([] , a)
  norm' (d ∷ ds) a with ⟨ decompose ⟩ a
  ... | left x = (d ∷ ds , a)
  ... | just x = norm' ds (x d)

  norm : ⟨ Mon A ⟩ -> ⟨ Mon A ⟩
  norm (ds , a) = norm' ds a



  private
    data isNormal : ⟨ Mon A ⟩ -> 𝒰 (𝑖 ⁺) where
       by-[] : ∀{a : ⟨ T ⟩ A} -> (depth a ≡ 0 -> 𝟘-𝒰) -> isNormal ([] , a)
       by-depth : ∀{ds} -> ∀{a : ⟨ T ⟩ A} -> depth a ≡ 0 -> isNormal (ds , a)

    lem::1 : ∀(a : ⟨ Mon A ⟩) -> isNormal a -> norm a ≡ a
    lem::1 ([] , a) P = refl
    lem::1 (d ∷ ds , a) (by-depth P) with ⟨ decompose ⟩ a | strict a
    ... | left a₂ | X = refl
    ... | just a₂ | X =
      let P₂ : depth (a₂ d) < depth a
          P₂ = X d

          P₃ : depth (a₂ d) < 0
          P₃ = transport (λ i -> depth (a₂ d) < P i) P₂

          P₄ : 𝟘-𝒰
          P₄ = P₃ .snd (≤0→≡0 (P₃ .fst))

      in 𝟘-elim P₄

    lem::2 : ∀(ds : ⟨ 𝔇 ⟩) -> (a : ⟨ T ⟩ A) -> isNormal (norm' ds a)
    lem::2 [] a with split-ℕ (depth a)
    ... | left x = by-depth x
    ... | just x = by-[] (λ a≡0 -> zero≢suc (a≡0 ⁻¹ ∙ snd x))
    lem::2 (d ∷ ds) a with ⟨ decompose ⟩ a | strict a
    ... | left x | P = by-depth (transport (λ i -> depth (P (~ i)) ≡ 0) depth/return)
    ... | just x | P = lem::2 ds (x d)

    lem::3 : ∀(a : ⟨ Mon A ⟩) -> norm (norm a) ≡ norm a
    lem::3 a = lem::1 (norm a) (lem::2 (fst a) (snd a))

  -}





{-
-------------- OLD TRY TO GET the (_∷ p) ≡ (_∷ q) -> p ≡ q working -------------------

      data QPath-≡ : ∀{k j} -> (p q : QPath {{of Q}} k j) -> 𝒰 𝑖 where
        last : ∀{k j} -> (e : Edge {{of Q}} k j) -> QPath-≡ (last e) (last e)
        _∷_ : ∀{l k j} -> (e : Edge {{of Q}} l k) -> {p q : QPath {{of Q}} k j}
              -> QPath-≡ p q -> QPath-≡ (e ∷ p) (e ∷ q)

      data QPath-≢ : ∀{k j} -> (p q : QPath {{of Q}} k j) -> 𝒰 𝑖 where
        last-≢ : ∀{k j} -> {e f : Edge {{of Q}} k j} -> (e ≢-Str f) -> QPath-≢ (last e) (last f)
        lengthMismatch-l : ∀{k l j} -> (e : Edge {{of Q}} k j) (f : Edge {{of Q}} k l) (p : QPath {{of Q}} l j)
                        -> QPath-≢ (last e) (f ∷ p)
        lengthMismatch-r : ∀{k l j} -> (e : Edge {{of Q}} k j) (f : Edge {{of Q}} k l) (p : QPath {{of Q}} l j)
                        -> QPath-≢ (f ∷ p) (last e)
        ∷-≢ : ∀{k l j} -> {e f : Edge {{of Q}} k l} {p q : QPath {{of Q}} l j} -> (e ≢-Str f) -> QPath-≢ (e ∷ p) (f ∷ q)
        nodeMismatch : ∀{k l1 l2 j} -> {e : Edge {{of Q}} k l1} {f : Edge {{of Q}} k l2} {p : QPath {{of Q}} l1 j} {q : QPath {{of Q}} l2 j} -> (l1 ≢-Str l2) -> QPath-≢ (e ∷ p) (f ∷ q)
        _∷_ : ∀{l k j} -> (e : Edge {{of Q}} l k) -> {p q : QPath {{of Q}} k j}
        -- _∷_ : ∀{k l1 l2 j} -> {e : Edge {{of Q}} k l1} {f : Edge {{of Q}} k l2} {p : QPath {{of Q}} l1 j} {q : QPath {{of Q}} l2 j}
              -> QPath-≢ p q -> QPath-≢ (e ∷ p) (e ∷ q)



      decide-QPath-≡ : ∀{k j} -> (p q : QPath {{of Q}} k j) -> (QPath-≢ p q) + (QPath-≡ p q)
      decide-QPath-≡ (last e) (last f) with e ≟-Str f
      ... | yes refl-StrId = right (last e)
      ... | no ¬p = left (last-≢ ¬p)
      decide-QPath-≡ (last e) (f ∷ p) = left (lengthMismatch-l e f p)
      decide-QPath-≡ (f ∷ p) (last e) = left (lengthMismatch-r e f p)
      decide-QPath-≡ (_∷_ {b = l1} e p) (_∷_ {b = l2} f q) with l1 ≟-Str l2
      ... | no ¬p = left (nodeMismatch ¬p)
      ... | yes refl-StrId with e ≟-Str f
      ... | no ¬p = left (∷-≢ ¬p)
      ... | yes refl-StrId with decide-QPath-≡ p q
      ... | left x = left (e ∷ x)
      ... | just x = right (e ∷ x)



      QPath-⊥ : ∀{k j} -> (p q : QPath {{of Q}} k j) -> (QPath-≢ p q) -> p ≡-Str q -> 𝟘-𝒰
      QPath-⊥ .(last _) .(last _) (last-≢ x) refl-StrId = x refl
      QPath-⊥ (e ∷ _) (f ∷ _) (∷-≢ x) S = {!!}
      QPath-⊥ .(_ ∷ _) .(_ ∷ _) (nodeMismatch x) refl-StrId = x refl
      QPath-⊥ .(e ∷ _) .(e ∷ _) (e ∷ R) S = {!!}
        -- where gg : ∀{k j} -> QPath {{of Q}} k j -> ∑ λ l -> Edge {{of Q}} k l
        --       gg (last x) = {!!}
        --       gg (x ∷ p) = _ , x

        --       P : (_ , e) ≡-Str (_ , f)
        --       P = cong-Str gg S

        --       P2 : e ≡-Str f
        --       P2 with cong-Str fst P
        --       ... | Z = {!!}

      -- QPath-≡-from-≡ : ∀{k j} -> (p q : QPath {{of Q}} k j) -> p ≡ q -> 


      -- lem-000-impl : ∀{k} -> ∀ j -> ∀ (e1 : Edge {{Dir}} k k) (e2 : Edge {{Dir}} k k) -> (p1 : QPath {{of Q}} k j) (p2 : QPath {{of Q}} k j)
      --           -> Path (QPath₊ k j) (some (e1 ∷ p1)) (some (e2 ∷ p2)) -> Path (QPath k j) p1 p2
      -- lem-000-impl {k} j e1 e2 p1 p2 q = {!!}

  {-
      lem-000-impl : ∀{k} -> ∀ j1 j2 -> ∀ (e1 : Edge {{Dir}} k k) (e2 : Edge {{Dir}} k k) -> (p1 : QPath {{of Q}} k j1) (p2 : QPath {{of Q}} k j2)
                -> (p : j1 ≡-Str j2) -> PathP (λ i -> QPath₊ k (≡-Str→≡ p i)) (some (e1 ∷ p1)) (some (e2 ∷ p2)) -> PathP (λ i -> QPath k (≡-Str→≡ p i)) p1 p2
      lem-000-impl {k} j1 .j1 e1 e2 p1 p2 refl-StrId q = {!!}

        where q2 : Path (QPath k j1) ((e1 ∷ p1)) ((e2 ∷ p2))
              q2 i = f (q i)
                  where f : (pp : QPath₊ {{of Q}} k j1) -> QPath {{of Q}} k j1
                        f id-Q = last a0
                        f (some x) = x

              q3 : ψ (e1 ∷ p1) ∼ ψ (e2 ∷ p2)
              q3 = fromPath {{isEquivRel:∼}} (cong ψ q2)

              P : ψ  ∼ ψ p2
              P with q3
              ... | nodes≡ , pat = {!!}

        -- where f : (pp : QPath₊ {{of Q}} k j1) -> QPath {{of Q}} k j1
        --       f id-Q = last a0
        --       f (some x) = {!!}
        --       -- f i .(some (e ∷ p)) (isEndoP e p) = p

      data fstIsEndo k j (p : QPath {{of Q}} k j) : 𝒰 𝑖 where
        isEndoP : (∀ l -> (e : Edge k l) -> (q : QPath {{of Q}} l j) -> (e ∷ q ≡ p) -> k ≡-Str l) -> fstIsEndo k j p

      -}



-}

