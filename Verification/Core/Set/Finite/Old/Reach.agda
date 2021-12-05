
module Verification.Core.Set.Finite.Old.Reach where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.HeytingAlgebra


-- 𝒫 : (A : 𝒰 𝑖) -> 𝒰 (𝑖 ⁺)
-- 𝒫 {𝑖} A = A -> Prop 𝑖

module _ {A : 𝒰 𝑖} where
  ⦅_⦆ : A -> A -> Prop 𝑖
  ⦅ a ⦆ b = ∣ (a ≡-Str b) ∣

  data Reachable : (p q : A -> Prop 𝑖) (_ : p ≤ q) -> 𝒰 (𝑖 ⁺) where
    refl-Reach : ∀{p q : A -> Prop 𝑖} -> (s : p ∼ q) -> (s' : p ≤ q) -> Reachable p q s'
    step-Reach : ∀{p q : A -> Prop 𝑖} -> ∀{a : A}
                 -> (p≤q : p ≤ q)
                 -> ⦅ a ⦆ ≰ p -> (Y : ⦅ a ⦆ ≤ q)
                 -> (w : p ∨ ⦅ a ⦆ ≤ q)
                 -> Reachable (p ∨ ⦅ a ⦆) q w
                 -> Reachable p q p≤q

    transp-Reach : ∀{p q p' q'} -> (p ∼ p') -> (q ∼ q') -> {a : p ≤ q} -> {b : p' ≤ q'} -> Reachable p q a -> Reachable p' q' b

  comp-Reach : ∀{p q r : A -> Prop 𝑖} {X : p ≤ q} {Y : q ≤ r} -> Reachable p q X -> Reachable q r Y -> Reachable p r (X ⟡ Y)
  comp-Reach (refl-Reach s s') q = refl-Reach {!!} {!!}
  comp-Reach (step-Reach _ x Y _ p) q = {!!} -- step-Reach ? x ? (comp-Reach p q)
  comp-Reach (transp-Reach x y p) = {!!}

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  Im : (A -> B) -> B -> Prop _
  Im f b = ∣ (∑ λ a -> f a ≡-Str b) ∣

module _ {A B : 𝒰 𝑖} {{_ : isDiscrete' B}} where

  private
    pb-Reach-impl : (f : A -> B) -> {p q : 𝒫 B} {{_ : is𝒫-Dec p}} {p' q' : 𝒫 A} -> (p' ≤ p ∣ f) -> (q ∣ f ∼ q')
                    -> {s : p' ≤ q'} -> {t : (p ∧ Im f) ≤ (q ∧ Im f)}
                    -> Reachable p' q' s -> Reachable (p ∧ Im f) (q ∧ Im f) t
    pb-Reach-impl f {p} {q} {p'} {q'} p'≤p q∼q' {_} {t} (refl-Reach s (incl v)) = refl-Reach (antisym t (incl P₀)) t --  (incl (⟨ t ⟩ , P₀)) t
      where
        P₀ : ∀ {a} -> ⟨ (q ∧ Im f) a ⟩ -> ⟨ (p ∧ Im f) a ⟩
        P₀ (qa , (b , refl-StrId)) =
          let -- X = {!!} -- ⟨ (q≤q' ⟡ (incl (⟨ ⟨ s {_} ⁻¹ ⟩ ⟩)) ⟡ p'≤p) ⟩ qa
              Y = ⟨ p'≤p ⟩ (⟨ ⟨ (s ⁻¹) ⟩ ⟩ (⟨ ⟨ q∼q' ⟩ ⟩ qa))
          in Y , (b , refl-StrId)

    pb-Reach-impl f {p} {q} {{pdec}} {p'} {q'} p'≤p q∼q' {_} {pf≤qf} (step-Reach {a = a} (p'≤q') a≰p' a≤q' p'a≤q' r) =
      let P₀ : (¬ ⟨ p (f a) ⟩) ∨ ⟨ p (f a) ⟩
          P₀ = decide-𝒫 {P = p} (f a)

          P₁ : (p' ∨ ⦅ a ⦆) ≤ (p ∨ ⦅ f a ⦆) ∣ f
          P₁ = incl (λ x → case x of
                            (λ x∈p' -> left (⟨ p'≤p ⟩ x∈p'))
                            (λ x∈a  -> right (cong-Str f x∈a)))

          R₀ : ∀ {i} -> (f a ≡-Str i) -> ⟨ q i ⟩
          R₀ {i} = λ {(refl-StrId) ->
              let Q₀ : ⟨ q' a ⟩
                  Q₀ = ⟨ a≤q' ⟩ refl

                  Q₁ : ⟨ q (f a) ⟩
                  Q₁ = ⟨ ⟨ q∼q' ⁻¹ ⟩ ⟩ Q₀
              in Q₁}

          P₂ : (p ∨ ⦅ f a ⦆) ∧ Im f ≤ q ∧ Im f
          P₂ = incl (λ {i} -> λ (x , y) →
              case x of
                (λ i∈p  -> let Q₀ : ⟨ (q ∧ Im f) i ⟩
                               Q₀ = ⟨ pf≤qf ⟩ (i∈p , y)
                           in (Q₀ .fst) , Q₀ .snd)
                (λ fa=i -> R₀ fa=i , y))

          r₁ = pb-Reach-impl f {p ∨ ⦅ f a ⦆} {q} {{it}} P₁ q∼q' {_} {P₂} r

          r₃ = case P₀ of
            (λ fa∉p ->
              let P₃ : ⦅ f a ⦆ ≰ p ∧ Im f
                  P₃ fa≤pf = fa∉p (⟨ fa≤pf ⟩ refl .fst)

                  P₄ : ⦅ f a ⦆ ≤ q ∧ Im f
                  P₄ = ⟨ incl (λ fa=i → R₀ fa=i) , (incl (λ fa=i → _ , fa=i)) ⟩-∧

                  P₅ : p ∧ Im f ∨ ⦅ f a ⦆ ≤ q ∧ Im f
                  P₅ = [ pf≤qf , P₄ ]-∨

                  P₆ : (p ∨ ⦅ f a ⦆) ∧ Im f ∼ p ∧ Im f ∨ ⦅ f a ⦆
                  P₆ = incl (λ {i} ->
                      ((λ (x , y) → case x of
                                          (λ x∈p -> left (x∈p , y))
                                          (λ fa=i -> right fa=i))
                      ,
                      (λ x -> case x of
                                    (λ (x∈p , x∈f) -> (left x∈p , x∈f))
                                    (λ (fa=i)      -> (right fa=i , (_ , fa=i))))))

                  r₂ = step-Reach pf≤qf P₃ P₄ P₅ (transp-Reach P₆ refl r₁)
              in r₂)
            (λ fa∈p ->
              let P₇ : p ∨ ⦅ f a ⦆ ∼ p
                  P₇ = antisym [ reflexive , incl (λ {refl-StrId -> fa∈p}) ]-∨ ι₀-∨
                  P₈ : (p ∨ ⦅ f a ⦆) ∧ Im f ∼ p ∧ Im f
                  P₈ = antisym (map-∧ (by-∼-≤ P₇) reflexive) (map-∧ (by-∼-≤ P₇ ⁻¹ ) reflexive)
              in transp-Reach P₈ refl r₁
              )
      in r₃

    pb-Reach-impl f {p} {q} {{pdec}} {p'} {q'} p'≤p q∼q' (transp-Reach {p''} {q''} p''∼p' q''∼q' r) =
      let P₀ : p'' ≤ p ∣ f
          P₀ = (by-∼-≤ p''∼p') ⟡ p'≤p

          P₁ : q ∣ f ∼ q''
          P₁ = q∼q' ∙ q''∼q' ⁻¹

          r₁ = pb-Reach-impl f {{pdec}} P₀ P₁ r
      in r₁

  rewrite-expre-𝒫 : {f : A -> B} -> {p q : 𝒫 B} -> ((p ∣ f) ≤ (q ∣ f)) -> (p ∧ Im f) ≤ (q ∧ Im f)
  rewrite-expre-𝒫 pf≤qf = incl (λ {i} -> λ {(i∈p , (_ , refl-StrId)) → ⟨ pf≤qf ⟩ i∈p , (_ , refl-StrId)})

  pb-Reach : (f : A -> B) -> (p q : 𝒫 B) {{_ : is𝒫-Dec p}}
                  -> {s : (p ∣ f) ≤ (q ∣ f)} -- -> {t : (p ∧ Im f) ≤ (q ∧ Im f)}
                  -> Reachable (p ∣ f) (q ∣ f) s -> Reachable (p ∧ Im f) (q ∧ Im f) (rewrite-expre-𝒫 s)
  pb-Reach f p q {s} r = pb-Reach-impl f reflexive refl r




