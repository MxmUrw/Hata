
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition

open import Verification.Core.Order.Preorder

-----------------------------------------
-- 人Vecᵖ

{-

record 人Vecᵖ (A : 𝒰 𝑖) (n : 人ℕ) : 𝒰 𝑖 where
  constructor vecᵖ
  field ⟨_⟩ : 人List A
  field hasSize : map-⋆List (const tt) ⟨_⟩ ≡ n

open 人Vecᵖ public

get-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (n ∍ i) -> A
get-人Vecᵖ = {!!}

get-∍-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (p : n ∍ i) -> ⟨ xs ⟩ ∍ get-人Vecᵖ xs p
get-∍-人Vecᵖ = {!!}

-}




{-
ι∀∍ : ∀{μs νs k i} -> (Γ : ℒHMCtx k μs) -> (k∍i : k ∍♮ i)
      -> ∀ {σ : μs ⟶ νs}
      -> ι (lookup-DList (Γ ⇃[ σ ]⇂-Ctx) k∍i .fst) ≅ ι (lookup-DList Γ k∍i .fst)
ι∀∍ (b ∷ Γ) incl = refl-≅
ι∀∍ (b ∷ Γ) (skip k∍i) = ι∀∍ Γ k∍i
-}


module §-ℒHMCtx where

--   prop-1 : ∀{μs νs k i}
--            -> {Q : ℒHMQuant k}
--            -> {Γ : ℒHMCtxFor Q μs} -> (k∍i : k ∍♮ i)
--            -> ∀ (σ₀ : μs ⟶ νs)
-- ⊔ (lookup-DList Q k∍i) 
--            -> lookup-DList Γ k∍i .snd ⇃[ σ ]⇂ ≡ lookup-DList (Γ ⇃[ ι₀ ◆ σ ]⇂-Ctx) k∍i .snd ⇃[ ⦗ id , ⟨ ι∀∍ Γ k∍i ⟩ ◆ ι₁ ◆ σ ⦘ ]⇂
--   prop-1 {Γ = (∀[ vα ] α) ∷ Γ} incl σ = ?

  --   let p : α ⇃[ (ι₀ ◆ σ) ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , id ◆ ι₁ ◆ σ ⦘ ]⇂ ≡ α ⇃[ σ ]⇂
  --       p = α ⇃[ (ι₀ ◆ σ) ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , id ◆ ι₁ ◆ σ ⦘ ]⇂ ⟨ functoriality-◆-⇃[]⇂ {τ = α} {f = (ι₀ ◆ σ) ⇃⊔⇂ id} {g = ⦗ id , id ◆ ι₁ ◆ σ ⦘} ⟩-≡
  --           α ⇃[ (ι₀ ◆ σ) ⇃⊔⇂ id ◆ ⦗ id , id ◆ ι₁ ◆ σ ⦘ ]⇂     ⟨ {!!} ⟩-≡
  --           -- call what we need here `append-⇃⊔⇂` vs `append-⇃⊓⇂`
  --           α ⇃[ σ ]⇂                                          ∎-≡
  --   in sym-Path p
  -- prop-1 {Γ = b ∷ Γ} (skip k∍i) σ = {!!}



  abstract
    prop-2 : ∀{μs νs : ℒHMTypes}
            -> ∀{k i} -> {Q : ℒHMQuant k}
            -> {Γ : ℒHMCtxFor Q μs} -> (k∍i : k ∍♮ i)
            -> ∀ (σ₀ : μs ⟶ νs)
            -> ∀ (σ₁ : lookup-DList Q k∍i ⟶ νs)
            ->  lookup-DDList (Γ ⇃[ σ₀ ]⇂-CtxFor) k∍i ⇃[ ⦗ id , σ₁ ⦘ ]⇂
              ≡
                lookup-DDList Γ k∍i ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
    prop-2 {Γ = b ∷ Γ} incl σ₀ σ₁ =
      let lem-0 : (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ∼ ⦗ σ₀ , σ₁ ⦘
          lem-0 = (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘   ⟨ append-⇃⊔⇂ {f0 = σ₀} {id} {id} {σ₁} ⟩-∼
                  ⦗ σ₀ ◆ id , id ◆ σ₁ ⦘       ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (unit-r-◆ {f = σ₀} , unit-l-◆ {f = σ₁}) ⟩-∼
                  ⦗ σ₀ , σ₁ ⦘                 ∎

          lem-1 : b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂ ≡ b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
          lem-1 = b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = b} {f = (σ₀ ⇃⊔⇂ id)} {g = ⦗ id , σ₁ ⦘} ⟩-≡
                  b ⇃[ (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ]⇂      ⟨ b ⇃[≀ lem-0 ≀]⇂ ⟩-≡
                  b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂                    ∎-≡
      in {!!} --  lem-1
    prop-2 {Γ = b ∷ Γ} (skip k∍i) σ₀ σ₁ = {!!} -- prop-2 {Γ = Γ} k∍i σ₀ σ₁

    prop-3 : ∀{μs νs : ℒHMTypes}
            -> ∀{k i} -> {Q : ℒHMQuant k}
            -> {Γ : ℒHMCtxFor Q μs} -> (k∍i : k ∍♮ i)
            -> ∀ (σ : μs ⊔ lookup-DList Q k∍i ⟶ νs)
            ->  lookup-DDList (Γ ⇃[ ι₀ ◆ σ ]⇂-CtxFor) k∍i ⇃[ ⦗ id , ι₁ ◆ σ ⦘ ]⇂
              ≡
                lookup-DDList Γ k∍i ⇃[ σ ]⇂
    prop-3 = {!!}






record ℒHMJudgementᵈ : 𝒰₀ where
  constructor _⊩_⊢_
  field metavars : ℒHMTypes
  field {contextsize} : ♮ℕ
  field context : ℒHMCtx contextsize metavars
  -- field quantifiers : DList (const (ℒHMTypes)) contextsize
  -- field context : DDList (λ a -> ℒHMType ⟨ a ⟩) quantifiers
  field type : ℒHMType ⟨ metavars ⟩

open ℒHMJudgementᵈ public

macro ℒHMJudgement = #structureOn ℒHMJudgementᵈ


sᵘ : ℒHMJudgement -> ♮ℕ
sᵘ (_ ⊩ Γ ⊢ τ) = size-DList (fst Γ)

macro s = #structureOn sᵘ


pattern _∷'_ x xs = _∷_ {a = tt} x xs
infix 30 ∀[]_
pattern ∀[]_ xs = ∀[ incl [] ] xs

record isAbstr {k} {Q : ℒHMQuant k} (κs : ℒHMTypes) {μs₀ μs₁} (Γ₀ : ℒHMCtxFor Q μs₀) (Γ₁ : ℒHMCtxFor Q μs₁)
               (τ₀ : ℒHMType ⟨ μs₀ ⟩) (τ₁ : ℒHMType ⟨ μs₁ ⊔ κs ⟩) : 𝒰₀ where
  constructor isAbstr:byDef
  field metasProof : μs₀ ≅ (μs₁ ⊔ κs)
  field ctxProof : Γ₀ ⇃[ ⟨ metasProof ⟩ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ
  field typeProof : τ₀ ⇃[ ⟨ metasProof ⟩ ]⇂ ≡ τ₁

  inverseCtxProof : Γ₀ ≡ Γ₁ ⇃[ ι₀ ◆ ⟨ metasProof ⟩⁻¹ ]⇂ᶜ
  inverseCtxProof = {!!}

open isAbstr public

module §-isAbstr where
  prop-1 : ∀{k} {Q : ℒHMQuant k} {κs : ℒHMTypes} {μs₀ μs₁ μs₂} {Γ₀ : ℒHMCtxFor Q μs₀} {Γ₁ : ℒHMCtxFor Q μs₁}
               {τ₀ : ℒHMType ⟨ μs₀ ⟩} {τ₁ : ℒHMType ⟨ μs₁ ⊔ κs ⟩}
           -> (σ₁₂ : μs₁ ⟶ μs₂)
           -> isAbstr κs Γ₀ Γ₁ τ₀ τ₁
           -> isAbstr κs Γ₀ (Γ₁ ⇃[ σ₁₂ ]⇂-CtxFor) τ₀ (τ₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂)
  prop-1 = {!!}

isInjective:∀[] : ∀{μs : ℒHMTypes} -> {α β : ℒHMType ⟨ μs ⊔ ⊥ ⟩} -> ∀[] α ≡ ∀[] β -> α ≡ β
isInjective:∀[] {α = α} {β} p = ≡-Str→≡ (lem-1 (≡→≡-Str p))
  where
    lem-1 : ∀[] α ≣ ∀[] β -> α ≣ β
    lem-1 refl-≣ = refl-≣

module _ {k νs} {Q : ℒHMQuant k} (Γ : ℒHMCtxFor Q νs) (τ : ℒHMType ⟨ νs ⟩) (κs : ℒHMTypes) where
  record Abstraction : 𝒰₀ where
    constructor abstraction
    field otherMetas : ℒHMTypes
    field otherCtx : ℒHMCtxFor Q otherMetas
    field otherType : ℒHMType ⟨ otherMetas ⊔ κs ⟩
    field isAbstrProof : isAbstr κs Γ otherCtx τ otherType
    -- field baseMetas : ℒHMTypes
    -- field extraMetas : ℒHMTypes
    -- field metasProof : (baseMetas ⊔ extraMetas) ≅ metavars 𝐽
    -- field baseCtx : ℒHMCtx _ baseMetas
    -- field baseCtxProof : baseCtx ⇃[ ι₀ ◆ ⟨ metasProof ⟩ ]⇂-Ctx ≡ context 𝐽
    -- field baseType : ℒHMType ⟨ baseMetas ⊔ extraMetas ⟩
    -- field baseTypeProof : baseType ⇃[ ⟨ metasProof ⟩ ]⇂ ≡ type 𝐽

open Abstraction public


data isTypedℒHMᵈ : (Γ : ℒHMJudgement) -> (te : UntypedℒHM (s Γ)) -> 𝒰₀ where
  var  : ∀{μs k i} -> {Q : ℒHMQuant k}
         -> {Γ : ℒHMCtxFor Q μs}
         -> (k∍i : k ∍♮ i)
         -> (σ : (lookup-DList Q k∍i) ⟶ μs)
         -> ∀{α}
         -> lookup-DDList Γ k∍i ⇃[ ⦗ id , σ ⦘ ]⇂ ≡ α
         -- -> Γ ⇃[ ι₀ ◆ σ ]⇂ᶜ ≡ Γ'
         -> isTypedℒHMᵈ ((μs) ⊩ (Q , Γ) ⊢ α) (var k∍i)

         -- -> lookup-DList Q k∍i ≣ vα
         -- (∀[ vα ] α)

{-
  gen : ∀{k μs te} {Γ₀ Γ₁ : ℒHMCtx k μs} {τ₀ τ₁ : ℒHMType ⟨ μs ⟩}
        -> isAbstr μs (μs ⊩ Γ₀ ⊢ τ₀) (μs ⊩ Γ₁ ⊢ τ₁)
        -> isTypedℒHMᵈ (μs ⊩ Γ₀ ⊢ τ₀) te
        -> isTypedℒHMᵈ (μs ⊩ Γ₁ ⊢ τ₁) te
-}

  app : ∀{μs k te₀ te₁} {Γ : ℒHMCtx k μs} {α β : ℒHMType ⟨ μs ⟩}
        -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ (α ⇒ β)) te₀
        -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ α) te₁
        -> isTypedℒHMᵈ (μs ⊩ Γ ⊢ β) (app te₀ te₁)

  lam : ∀{μs k te} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μs}
         {α : ℒHMType ⟨ μs ⊔ ⊥ ⟩}
         {β : ℒHMType ⟨ μs ⟩}
         -> isTypedℒHMᵈ (μs ⊩ (⊥ ∷' Q , α ∷ Γ) ⊢ β) te
         -> isTypedℒHMᵈ (μs ⊩ (Q , Γ) ⊢ α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β) (lam te)

  slet : ∀{μs κs νs k te₀ te₁}
        -> {Q : ℒHMQuant k}
        -> {Γ : ℒHMCtxFor Q μs} {Γ' : ℒHMCtxFor Q νs}
        -> {α : ℒHMType ⟨ μs ⟩}
        -> {α' : ℒHMType ⟨ νs ⊔ κs ⟩}
        -> {β : ℒHMType ⟨ νs ⟩}
        -> isAbstr (κs) (Γ) (Γ') α α'
        -> isTypedℒHMᵈ (μs ⊩ (Q , Γ) ⊢ α) te₀
        -> isTypedℒHMᵈ (νs ⊩ (κs ∷' Q , α' ∷ Γ') ⊢ β) te₁
        -> isTypedℒHMᵈ (νs ⊩ (Q , Γ') ⊢ β) (slet te₀ te₁)

{-
-}

isTypedℒHM = isTypedℒHMᵈ

transp-isTypedℒHM : ∀{k μs te} {Q : ℒHMQuant k}
         -> {Γ₀ : ℒHMCtxFor Q μs} {τ₀ : ℒHMType ⟨ μs ⟩}
         -> {Γ₁ : ℒHMCtxFor Q μs} {τ₁ : ℒHMType ⟨ μs ⟩}
         -> Γ₀ ≡ Γ₁ -> τ₀ ≡ τ₁
         -> isTypedℒHM (μs ⊩ (_ , Γ₀) ⊢ τ₀) te
         -> isTypedℒHM (μs ⊩ (_ , Γ₁) ⊢ τ₁) te
transp-isTypedℒHM = {!!}


module §-isTypedℒHM where
  abstract
    prop-1 : ∀{μs k} -> {Γ : ℒHMCtx k μs} {τ : ℒHMType ⟨ μs ⟩}
            -> ∀ te
            -> isTypedℒHM (μs ⊩ Γ ⊢ τ) (lam te)
            -> ∑ λ νs -> ∑ λ (Δ : ℒHMCtx (tt ∷ k) νs) -> ∑ λ (τ' : ℒHMType ⟨ νs ⟩)
            -> isTypedℒHM (νs ⊩ Δ ⊢ τ') te
    prop-1 te (lam p) = {!!} , ({!!} , ({!!} , p))


    prop-2 : ∀{k μs νs te} {Γ : ℒHMCtx k μs} {τ : ℒHMType ⟨ μs ⟩}
          -> (σ : μs ⟶ νs)
          -> isTypedℒHM (μs ⊩ Γ ⊢ τ) te
          -> isTypedℒHM (νs ⊩ (Γ ⇃[ σ ]⇂-Ctx) ⊢ (τ ⇃[ σ ]⇂)) te
    prop-2 σ (var x xp ρ) = {!!}
    prop-2 σ (app te se) =
      let te' = prop-2 σ te
          se' = prop-2 σ se
      in app te' se'
    prop-2 σ (lam te) = {!!}
    prop-2 σ (slet ab set te) = {!!}

    prop-4 : ∀{k μsₐ μsₓ νsₓ νsₐ te} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μsₐ} {τ : ℒHMType ⟨ μsₐ ⊔ μsₓ ⟩}
          -> (σₐ : μsₐ ⟶ νsₐ)
          -> (σₓ : μsₓ ⟶ νsₓ)
          -> isTypedℒHM (μsₐ ⊔ μsₓ ⊩ (_ , Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ τ) te
          -> isTypedℒHM (νsₐ ⊔ νsₓ ⊩ (_ , Γ ⇃[ σₐ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ (τ ⇃[ σₐ ⇃⊔⇂ σₓ ]⇂)) te
    prop-4 = {!!}

    prop-3 : ∀{k μsₐ μsₓ νsₓ te} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μsₐ} {τ : ℒHMType ⟨ μsₐ ⊔ μsₓ ⟩}
          -> (σ : μsₓ ⟶ νsₓ)
          -> isTypedℒHM (μsₐ ⊔ μsₓ ⊩ (_ , Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ τ) te
          -> isTypedℒHM (μsₐ ⊔ νsₓ ⊩ (_ , Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ (τ ⇃[ id ⇃⊔⇂ σ ]⇂)) te
    prop-3 = {!!}


  -- let res = prop-2 σ te
  --                     in lam {!!} -- res

  -- prop-2 σ (slet ab te se) = {!!}


InitialAbstraction : ∀{νs k} {Q : ℒHMQuant k} -> (Γ : ℒHMCtxFor Q νs)
                     -> (τ : ℒHMType ⟨ νs ⟩) -> 𝒰₀
InitialAbstraction Γ τ = ∑ λ (ab : ∑ Abstraction Γ τ) -> ∀(ab' : ∑ Abstraction Γ τ) -> fst ab ⟶ fst ab'

abstr-Ctx : ∀{νs k} {Q : ℒHMQuant k} -> (Γ : ℒHMCtxFor Q νs)
          -> (τ : ℒHMType ⟨ νs ⟩)
          -- -> ∑ λ μsa -> ∑ λ μsb -> ∑ λ (Γ' : ℒHMCtxFor Q μsa) -> ∑ λ (τ' : ℒHMType ⟨ μsa ⊔ μsb ⟩)
          -- -> (isAbstr _ Γ Γ' τ τ')
          -- (ab : ∑ Abstraction Γ τ) -> ∀(ab' : ∑ Abstraction Γ τ) -> fst ab ⟶ fst ab'
          -> InitialAbstraction Γ τ
abstr-Ctx = {!!}

{-

-}

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
--         ∷ map-ℒHMCtx σ Γ
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

