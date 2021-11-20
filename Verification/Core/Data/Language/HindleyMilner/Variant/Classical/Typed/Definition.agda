
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition

-----------------------------------------
-- 人Vecᵖ

{-

record 人Vecᵖ (A : 𝒰 𝑖) (n : 人ℕ) : 𝒰 𝑖 where
  constructor vecᵖ
  field ⟨_⟩ : 人List A
  field hasSize : map-Free-𝐌𝐨𝐧 (const tt) ⟨_⟩ ≡ n

open 人Vecᵖ public

get-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (n ∍ i) -> A
get-人Vecᵖ = {!!}

get-∍-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (p : n ∍ i) -> ⟨ xs ⟩ ∍ get-人Vecᵖ xs p
get-∍-人Vecᵖ = {!!}

-}

module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-D人List : ∀{m} -> D人List F m -> 人List A
  size-D人List {m} _ = m

module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-DList : ∀{m} -> DList F m -> List A
  size-DList {m} _ = m


record ℒHMJudgementᵈ : 𝒰₀ where
  constructor _⊩_⊢_
  field metavars : ℒHMTypes
  field {contextsize} : ♮ℕ
  field context : DList (const (ℒHMPolyType metavars)) contextsize
  -- ℒHMCtx' metavars
  field type : ℒHMPolyType metavars

open ℒHMJudgementᵈ public

macro ℒHMJudgement = #structureOn ℒHMJudgementᵈ

-- instance
--   isCategory:ℒHMJudgement : isCategory {ℓ₀ , ℓ₀} ℒHMJudgement
--   isCategory:ℒHMJudgement = {!!}

sᵘ : ℒHMJudgement -> ♮ℕ
sᵘ (_ ⊩ Γ ⊢ τ) = size-DList Γ

macro s = #structureOn sᵘ

-- ℒHMJudgementCategory : 𝐂𝐚𝐭₀
-- ℒHMJudgementCategory = ℒHMJudgement

pattern _∷'_ x xs = _∷_ {a = tt} x xs
infix 30 ∀[]_
pattern ∀[]_ xs = ∀[ incl [] ] xs

data isAbstr (m : ℒHMTypes) : (a b : ℒHMJudgement) -> 𝒰₀ where
  -- incl : ∀{k n} -> ∀{τ : ℒHMPolyType (n ⊔ m)} -> ∀{Γ : ℒHMCtx' n k}
  --        -> isAbstr m (mapOf ℒHMCtx' ι₀ μs ⊩ Γ ⊢ τ) (μs ⊩ Γ ⊢ abstr τ)

data isTypedℒHMᵈ : (Γ : ℒHMJudgement) -> (te : UntypedℒHM (s Γ)) -> 𝒰₀ where
  var  : ∀{μs k} -> {Γ : ℒHMCtx' k μs} {α : ℒHMPolyType μs}
         -- -> Γ ∍ α
         -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ α) var


  gen : ∀{k μs te} {Γ₀ Γ₁ : ℒHMCtx' k μs} {τ₀ τ₁ : ℒHMPolyType μs}
        -> isAbstr μs (μs ⊩ Γ₀ ⊢ τ₀) (μs ⊩ Γ₁ ⊢ τ₁)
        -> isTypedℒHMᵈ (μs ⊩ Γ₀ ⊢ τ₀) te
        -> isTypedℒHMᵈ (μs ⊩ Γ₁ ⊢ τ₁) te

  app : ∀{μs k te₀ te₁} {Γ : ℒHMCtx' k μs} {α β : Term₁-𝕋× 𝒹 (⟨ μs ⟩ ⋆ ◌) tt}
        -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ ∀[ (incl ◌) ] (α ⇒ β)) te₀
        -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ ∀[ (incl ◌) ] α) te₁
        -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ ∀[ (incl ◌) ] β) (app te₀ te₁)

{-
  lam : ∀{μs k} {Γ : ℒHMCtx' k μs} {α β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
        -> isTypedℒHMᵈ (μs ⊩ ((∀[] α) ∷' Γ) ⊢ ∀[] β)
        -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ ∀[] α ⇒ β)
        -}


  lam2 : ∀{μs k vβ te} {Γ : ℒHMCtx' k μs}
         {α : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
         {β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ι vβ ⟩ tt}
         -> isTypedℒHMᵈ (μs ⊩ ((∀[] α) ∷' Γ) ⊢ ∀[ vβ ] β) te
         -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ ∀[ vβ ] (α ⇃[ id {a = μs} ⇃⊔⇂ elim-⊥ ]⇂) ⇒ β) (lam te)

{-
  -- convert : ∀{m0 m1 k} -> (m0 ⟶ m1) -> {Γ₀ : ℒHMCtx' k m0} -> ∀{τ₀} -> {Γ₁ : ℒHMCtx' k m1} -> ∀{τ₁}
  --           -> isTypedℒHMᵈ (m0 ⊩ Γ₀ ⊢ τ₀)
  --           -> isTypedℒHMᵈ (m1 ⊩ Γ₁ ⊢ τ₁)

  mapmeta : ∀{k μs νs} (ϕ : μs ⟶ νs) -> {Γ₀ : ℒHMCtx' k μs} -> ∀{τ₀}
            -> isTypedℒHMᵈ (μs ⊩ Γ₀ ⊢ τ₀)
            -> isTypedℒHMᵈ (νs ⊩ mapOf (ℒHMCtx' k) ϕ Γ₀ ⊢ mapOf ℒHMPolyType ϕ τ₀)

  instantiate : ∀{μs k} {Γ : ℒHMCtx' k μs} {α β : ℒHMPolyType μs}
         -> (α ⟶ β)
         -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ α)
         -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ β)
-}
-- instance
--   isCategory:TypedℒHM : ∀{X Γ} -> isCategory {ℓ₀ , ℓ₀} (isTypedℒHMᵈ Γ)
--   isCategory:TypedℒHM = {!!}

isTypedℒHM = isTypedℒHMᵈ

module §-isTypedℒHM where
  prop-1 : ∀{μs k} -> {Γ : ℒHMCtx' k μs} {τ : ℒHMPolyType μs}
           -> ∀ te
           -> isTypedℒHM (μs ⊩ Γ ⊢ τ) (lam te)
           -> ∑ λ νs -> ∑ λ (Δ : ℒHMCtx' (tt ∷ k) νs) -> ∑ λ (τ' : ℒHMPolyType νs)
           -> isTypedℒHM (νs ⊩ Δ ⊢ τ') te
  prop-1 te (lam2 p) = {!!} , ({!!} , ({!!} , p))


  prop-2 : ∀{k μs νs te} {Γ : ℒHMCtx' k μs} {τ : ℒHMPolyType μs}
         -> (σ : μs ⟶ νs)
         -> isTypedℒHM (μs ⊩ Γ ⊢ τ) te
         -> isTypedℒHM (νs ⊩ (Γ ⇃[ σ ]⇂-Ctx) ⊢ (τ ⇃[ σ ]⇂-poly)) te
  prop-2 σ var = {!!}
  prop-2 σ (app te se) =
    let te' = prop-2 σ te
        se' = prop-2 σ se
    in app te' se'
  prop-2 σ (lam2 te) = {!!} --  let res = prop-2 σ te
                        -- in lam2 res

  -- isTypedℒHM
  -- (νs ⊩ Γ ⇃[ σ ]⇂-Ctx ⊢
  --  ((∀[ fst₁ ]
  --    con ⇒ᵗ
  --    (incl
  --     (α ⇃[
  --      isCategory.id
  --      (Verification.Core.Category.Std.Functor.Faithful.isCategory:byFaithful
  --       Hom-⧜𝐒𝐮𝐛𝐬𝐭' id-⧜𝐒𝐮𝐛𝐬𝐭 _◆-⧜𝐒𝐮𝐛𝐬𝐭_ ι-⧜𝐒𝐮𝐛𝐬𝐭ᵘ map-ι-⧜𝐒𝐮𝐛𝐬𝐭
  --       Verification.Core.Data.Substitution.Variant.Base.Definition.lem-03
  --       Verification.Core.Data.Substitution.Variant.Base.Definition.lem-02)
  --      ⇃⊔⇂
  --      isInitial.elim-⊥
  --      (hasInitial.isInitial:⊥
  --       Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition.hasInitial:byFFEso)
  --      ]⇂)
  --     ⋆-⧜ (incl β ⋆-⧜ ◌-⧜)))
  --   ⇃[ σ ]⇂-poly))
  -- (lam te₁)


-- res  : isTypedℒHMᵈ
--        (νs ⊩
--         (∀[]
--          𝕋×.統.reext-Term-𝕋×
--          (λ i x →
--             destruct-D人List
--             (construct-D人List
--              (λ a x₁ →
--                 destruct-D人List
--                 (construct-D人List
--                  (λ i₁ a₁ →
--                     𝕋×.統.reext-Term-𝕋×
--                     (λ i₂ x₂ →
--                        destruct-D人List (construct-D人List (λ i₃ a₂ → var (left-∍ a₂))) i₂
--                        x₂)
--                     i₁ (destruct-D人List ⟨ σ ⟩ i₁ a₁)))
--                 a x₁)
--              ⋆-⧜ ◌-⧜)
--             i x)
--          tyᵗ α)
--         ∷ map-ℒHMCtx' σ Γ
--         ⊢
--         (∀[ fst₁ ]
--          𝕋×.統.reext-Term-𝕋×
--          (λ i x →
--             destruct-D人List
--             (construct-D人List
--              (λ a x₁ →
--                 destruct-D人List
--                 (construct-D人List
--                  (λ i₁ a₁ →
--                     𝕋×.統.reext-Term-𝕋×
--                     (λ i₂ x₂ →
--                        destruct-D人List (construct-D人List (λ i₃ a₂ → var (left-∍ a₂))) i₂
--                        x₂)
--                     i₁ (destruct-D人List ⟨ σ ⟩ i₁ a₁)))
--                 a x₁)
--              ⋆-⧜
--              construct-D人List
--              (λ a x₁ →
--                 destruct-D人List
--                 (construct-D人List
--                  (λ i₁ a₁ →
--                     𝕋×.統.reext-Term-𝕋×
--                     (λ i₂ x₂ →
--                        destruct-D人List (construct-D人List (λ i₃ a₂ → var (right-∍ a₂))) i₂
--                        x₂)
--                     i₁ (destruct-D人List (construct-D人List (λ i₂ x₂ → var x₂)) i₁ a₁)))
--                 a x₁))
--             i x)
--          tyᵗ β))
--        te₁




{-

record ℒHMJudgement : 𝒰₀ where
  constructor _⊢_
  field {metavars} : ℒHMTypes
  field context : ℒHMCtx metavars
  field type : ℒHMPolyType metavars

open ℒHMJudgement public

data isAbstr (m : ℒHMTypes) : (a b : ℒHMJudgement) -> 𝒰₀ where
  incl : ∀{n} -> ∀{τ : ℒHMPolyType (n ⊔ m)} -> ∀{Γ : ℒHMCtx n}
         -> isAbstr m (mapOf ℒHMCtx ι₀ μs ⊩ Γ ⊢ τ) (μs ⊩ Γ ⊢ abstr τ)

data isTypedℒHMᵈ (X : ℒHMJudgement -> 𝒰₀) : (Γ : ℒHMJudgement) -> 𝒰₀ where
  var  : ∀{μs} -> {Γ : ℒHMCtx μs} {α : ℒHMPolyType μs}
         -> Γ ∍ α -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ α)

  hole : ∀{Γ} -> X Γ -> isTypedℒHMᵈ Γ

  gen : ∀{m a b} -> isAbstr m a b -> TypedℒHMᵈ X a -> TypedℒHMᵈ X b

  app : ∀{μs} {Γ : ℒHMCtx μs} {α β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] (α ⇒ β))
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] α)
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] β)

  lam : ∀{μs} {Γ : ℒHMCtx μs} {α β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X ((Γ ⋆ incl (∀[ ⊥ ] α)) ⊢ ∀[ ⊥ ] β)
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] α ⇒ β)

  convert : ∀{m0 m1} -> (m0 ⟶ m1) -> {Γ₀ : ℒHMCtx m0} -> ∀{τ₀} -> {Γ₁ : ℒHMCtx m1} -> ∀{τ₁}
            -> TypedℒHMᵈ X (Γ₀ ⊢ τ₀)
            -> TypedℒHMᵈ X (Γ₁ ⊢ τ₁)

  instantiate : ∀{μs} {Γ : ℒHMCtx μs} {α β : ℒHMPolyType μs}
         -> (α ⟶ β)
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ α)
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ β)

-}

-- isTypedℒHM : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
-- isTypedℒHM A = indexed (TypedℒHMᵈ (ix A))

-- macro TypedℒHM = #structureOn TypedℒHMᵘ



-- module mytest where
--   Γ : ℒHMCtx ⊥
--   Γ = ◌

  -- mytest : TypedℒHMᵈ (const ⊥-𝒰) (μs ⊩ Γ ⊢ ∀[ incl (incl tyᵗ) ] var (right-∍ incl) ⇒ var (right-∍ incl))
  -- mytest = convert id (gen incl (lam (var (right-∍ incl))))


-- TypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
-- TypedℒHMᵘ A = indexed (TypedℒHMᵈ (ix A))

-- macro TypedℒHM = #structureOn TypedℒHMᵘ


