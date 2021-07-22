
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaChurch.Instance.MTC2 where

open import Verification.Experimental.Conventions hiding (Maybe)
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Sum.Instance.Monad
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.Monoidal
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
-- open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition
import Verification.Experimental.Theory.Std.Specific.Simple.LambdaChurch.Definition as Λ
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaChurch.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Instance.LogicalFramework
open import Verification.Experimental.Theory.Std.Generic.LogicalFramework.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.Monoidal.Definition
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition
open import Verification.Experimental.Data.Lift.Definition
open import Verification.Experimental.Data.Type.Definition

Maybe : 𝒰 𝑖 -> 𝒰 𝑖
Maybe {𝑖} A = ⊤-𝒰 {𝑖} + A

module Λ-Church where

  data Kind {𝑖} : 𝒰 𝑖 where
    Tek : Kind
    Tyk : Kind

  instance
    isKinding:Kind : isKinding (Kind {𝑖})
    isKinding:Kind = record { ∂ₖ = const Tyk }

  -- relevel-Kind : Kind {𝑖} -> Kind {𝑗}
  -- relevel-Kind Te = Te
  -- relevel-Kind VarSuc = VarSuc
  -- relevel-Kind VarZero = VarZero

  -- data isGood' : Type-MTC Kind -> ℕ -> 𝒰₀ where
  --   zero : ∀ {k} -> isGood' (kind k) 0
  --   suc : ∀{k τ} -> isGood' τ n -> isGood' (kind k ⇒ τ) (suc n)

  -- isGood : Type-MTC Kind -> 𝒰₀
  -- isGood τ = ∑ isGood' τ
  -- Good = const 𝟙-𝒰
  -- postulate
  --   GApp : isGood (kind Te ⇒ (kind Te ⇒ kind Te))
  --   GLam : isGood ((kind Te ⇒ kind Te) ⇒ kind Te)
  --   GAll : ∀{τ} -> isGood τ

  data Ty (A : 𝒰₀) : 𝒰₀ where
    `ℕ` : Ty A
    _`⇒`_ : Ty A -> Ty A -> Ty A
    var : A -> Ty A


  data TermCon-Λ {𝑖} : List (Judgement (Kind {𝑖})) → Judgement (Kind {𝑖}) → 𝒰 𝑖 where
    App : TermCon-Λ ⦋ (⦋⦌ ⊢ Tek) ، (⦋⦌ ⊢ Tek)⦌ (⦋⦌ ⊢ Tek)
    Lam : TermCon-Λ ⦋ ⦋ Tek ⦌ ⊢ Tek ⦌ (⦋⦌ ⊢ Tek)
    Suc : TermCon-Λ ⦋ ⦋⦌ ⊢ Tek ⦌ (⦋⦌ ⊢ Tek)
    Zero : TermCon-Λ ⦋⦌ (⦋⦌ ⊢ Tek)
    False True : TermCon-Λ ⦋⦌ (⦋⦌ ⊢ Tek)
    Rec-ℕ : TermCon-Λ
            ⦋ ⦋⦌ ⊢ Tyk ، ⦋ Tek ⦌ ⊢ Tek ، ⦋⦌ ⊢ Tek ، ⦋⦌ ⊢ Tek ⦌
            --------------------------------------
            (⦋⦌ ⊢ Tek)

    `ℕ` `𝔹` : TermCon-Λ ⦋⦌ (⦋⦌ ⊢ Tyk)
    `⇒` : TermCon-Λ ⦋ ⦋⦌ ⊢ Tyk ، ⦋⦌ ⊢ Tyk ⦌ (⦋⦌ ⊢ Tyk)



  private
    Λ : MetaTermCalculus ′ Kind {𝑖} ′ 𝑖
    Λ = record { TermCon = TermCon-Λ }

  module Proof-of-correct-terms {𝑖} where

    open MTCDefinitions (Λ {𝑖})

    -- TyToTy-⨯ : ℕ -> Type-MTC {𝑖} Kind
    -- TyToTy-⨯ = ?
    -- TyToTy-⨯ zero = kind Te
    -- TyToTy-⨯ (suc n) = kind Te ⇒ TyToTy-⨯ n

    TyToCtx-⨯ : ℕ -> List (Kind {𝑖})
    TyToCtx-⨯ 0 = []
    TyToCtx-⨯ (suc n) = Tek ∷ TyToCtx-⨯ n
    -- TyToCtx-⨯ = ?
    -- TyToCtx-⨯ zero = []
    -- TyToCtx-⨯ (suc n) = TyToCtx-⨯ n ,, kind Te

    infixl 8 _$$_
    pattern _$$_ a b = app a b

    TermToTerm-var : ∀{n} (i : 𝔽ʳ n) -> TyToCtx-⨯ n ⊨-var Tek
    TermToTerm-var zero = zero
    TermToTerm-var (suc i) = suc (TermToTerm-var i)

    TyToTerm : ∀{Γ} -> Ty-λ {𝑘} -> [] ⊩ᶠ (Γ ∣ [] ⇒ ([] ⊢ Tyk))
    TyToTerm `ℕ` = con `ℕ`
    TyToTerm `𝔹` = con `𝔹`
    TyToTerm (ty `⇒` ty₁) = con `⇒` $$ TyToTerm ty $$ TyToTerm ty₁


    TermToTerm-⨯ : ∀{n} -> Λ.Term-λ n -> [] ⊩ᶠ (TyToCtx-⨯ n ∣ [] ⇒ ([] ⊢ Tek))
    TermToTerm-⨯ (app f x)   = (con App) $$ (TermToTerm-⨯ f) $$ (TermToTerm-⨯ x)
    TermToTerm-⨯ (lam ty te) = app (con Lam) (lam (TyToTerm ty) (TermToTerm-⨯ te))
    TermToTerm-⨯ (var x)     = var (TermToTerm-var x)
    TermToTerm-⨯ zero        = con Zero
    TermToTerm-⨯ false        = con False
    TermToTerm-⨯ true        = con True
    TermToTerm-⨯ (suc te)    = app (con Suc) (TermToTerm-⨯ te)
    TermToTerm-⨯ (rec-ℕ ty te te₁ te₂) = (con Rec-ℕ) $$ (TyToTerm ty) $$ (lam (TyToTerm ty) (TermToTerm-⨯ te)) $$ TermToTerm-⨯ te₁ $$ TermToTerm-⨯ te₂


  instance
    _ = isCwJ:MTCCat

  ΛTT : TypeTheory-⊗ ′(Kind {ℓ₀})′ _ _
  TypeTheory-⊗.𝒯erm ΛTT = MTCCat Λ since isCwJ:MTCCat
  TypeTheory-⊗.𝒯ype ΛTT = TheCwJ (const (Ty-λ {ℓ₀})) id
  TypeTheory-⊗.typing ΛTT = MTC-λ₋2.Proof (TheCwJ (const (Ty-λ {ℓ₀})) id) f
    where
      f : Hom-MTC Λ _
      f = record { ⟨_⟩ = g }
        where
          now : ∀{A B : 𝒰 𝑘} -> (A -> ⊤-𝒰 {𝑘} + B) -> KleisliHom {T = (⊤-𝒰 {𝑘} +⧿)} (incl A) (incl (◌ ⋆ B))
          now f = incl (λ a  -> do res <- f a
                                   return (tt , res))


          checkSuc : ◌ ⋆ Ty-λ ⋆ ◌ -> Maybe Ty-λ
          checkSuc ((_ , `ℕ`) , _) = just `ℕ`
          checkSuc (_ , _) = nothing

          checkLam : Ty-λ ⋆ ◌ ⋆ Ty-λ ⋆ ◌ -> Maybe Ty-λ
          checkLam (((a , _) , b) , _) = just (_`⇒`_ a b)

          checkApp : ((◌ ⋆ Ty-λ) ⋆ ((◌ ⋆ Ty-λ) ⋆ ◌)) -> Maybe Ty-λ
          checkApp ((_ , (a `⇒` a₁)) , (_ , b) , _) with a ≟ b
          ... | true  = right a₁
          ... | false = left tt
          checkApp ((_ , x) , (_ , b) , _) = left tt


          g : {Δ : List (Judgement Kind)} {α : Judgement Kind} → TermCon-Λ Δ α → _
          g App = now checkApp
          g Lam = now checkLam
          g Suc = now checkSuc
          g Zero = incl (λ x → right (tt , `ℕ`))
          g False = now (const (right `𝔹`))
          g True = now (const (right `𝔹`))
          g Rec-ℕ = {!!}
          g `ℕ` = now (const (right `ℕ`))
          g `𝔹` = now (const (right `𝔹`))
          g `⇒` = now λ ((_ , a) , (_ , b) , _) → right (_`⇒`_ a b)

  checkChurch : Term-λ 0 -> _
  checkChurch te =
    let te' = Proof-of-correct-terms.TermToTerm-⨯ {𝑖 = ℓ₀} te
        te'' = map {{of typing {{ΛTT}}}} (te' ∷ [])
    in do ((_ , res) , _) <- ⟨ te'' ⟩ tt
          return res


mytest1 : Term-λ 0
mytest1 = lam `𝔹` (suc (suc (var zero)))

mytest1-c = Λ-Church.checkChurch mytest1

  -- TypeTheory-⊗.𝒯erm ΛTT = LFTerm Λ
  -- TypeTheory-⊗.Types ΛTT = hasJudgements:𝐓𝐲𝐩𝐞
  -- TypeTheory-⊗.typing ΛTT = interp myi


{-
  data TyCtx {𝑗} : (G : Ctx-⦿ (Kind {𝑗})) -> 𝒰 𝑗 where
    [] : TyCtx []
    _,,_ : ∀{Γ} -> TyCtx Γ -> Ty (𝔽ʳ 0) -> TyCtx (Γ ,, Te)


  -- io : Jdg-⦿ (Lift {𝑖 ⁺} (Kind {𝑖})) -> 𝒰 _
  -- io (Γ ⊢ ↥ Te) = TyCtx (map-Ctx-⦿ lower Γ) ×-𝒰 (Ty (𝔽ʳ 0))
  -- io (Γ ⊢ ↥ VarSuc) = Lift (Ty (𝔽ʳ 0))
  -- io (Γ ⊢ ↥ VarZero) = TyCtx (map-Ctx-⦿ lower Γ)


  io : Jdg-⦿ ((Kind {𝑖})) -> 𝒰 _
  io (Γ ⊢ Te) = TyCtx (Γ) ×-𝒰 (Ty (𝔽ʳ 0))
  io (Γ ⊢ VarSuc) = Lift (Ty (𝔽ʳ 0))
  io (Γ ⊢ VarZero) = TyCtx (Γ)

  private instance
    hasJudgements:𝐓𝐲𝐩𝐞 : hasJudgements {𝑗 ⁺} (𝐓𝐲𝐩𝐞' 𝑗)
    hasJudgements:𝐓𝐲𝐩𝐞 {𝑗} = record { JKind = Kind ; JObj = λ x -> lift (io (map-Jdg-⦿ relevel-Kind x)) }

  myi-TermCon : (ρ : Rule-⦿ (Kind {𝑖 ⁺})) →
                TermCon-Λ ρ →
                iFam {𝒞 = 𝐓𝐲𝐩𝐞' 𝑖} (λ x → lift (io (map-Jdg-⦿ relevel-Kind x)))
                (map-Rule-⦿ id-𝒰 ρ)
  myi-TermCon .(⦋ ⦋⦌ ⊢ Te ، ⦋⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) App = {!!}
  myi-TermCon .(⦋ ⦋ Te ⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) Lam = {!!}
  myi-TermCon .(⦋ ⦋⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) Suc = {!!}
  myi-TermCon .(⦋ ⦋⦌ ⊢ VarZero ⦌ ⊩ ⦋⦌ ⊢ Te) Zero = λ Δ' → incl λ (a , Δ) → Δ , `ℕ`
  myi-TermCon .(⦋ ⦋ Te ⦌ ⊢ Te ، ⦋⦌ ⊢ Te ، ⦋⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) Rec-ℕ = {!!}
  -- myi-TermCon .(⦋ ⦋⦌ ⊢ Te ، ⦋⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) App = {!!}
  -- myi-TermCon .(⦋ ⦋ Te ⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) Lam = {!!}
  -- myi-TermCon .(⦋ ⦋⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) Suc = {!!}
  -- myi-TermCon .(⦋⦌ ⊩ ⦋⦌ ⊢ Te) Zero = {!!}
  -- myi-TermCon .(⦋ ⦋ Te ⦌ ⊢ Te ، ⦋⦌ ⊢ Te ، ⦋⦌ ⊢ Te ⦌ ⊩ ⦋⦌ ⊢ Te) Rec-ℕ = {!!}

  myi : Λ ⟶ (LFSig {{isLogicalFramework:MTC}} (𝐓𝐲𝐩𝐞' 𝑗))
  myi = id since record {
    map-varzero = {!!}
    ; map-varsuc = {!!}
    ; map-TermCon = myi-TermCon
    }


  ΛTT : TypeTheory-⊗ 𝑖
  TypeTheory-⊗.𝒯erm ΛTT = LFTerm Λ
  TypeTheory-⊗.Types ΛTT = hasJudgements:𝐓𝐲𝐩𝐞
  TypeTheory-⊗.typing ΛTT = interp myi








  module Proof-of-correct-terms {𝑖} where

    open MTCDefinitions (Λ {𝑖})

    TyToTy-⨯ : ℕ -> Type-MTC {𝑖} Kind
    TyToTy-⨯ zero = kind Te
    TyToTy-⨯ (suc n) = kind Te ⇒ TyToTy-⨯ n

    TyToCtx-⨯ : ℕ -> Ctx-⦿ (Type-MTC {𝑖} Kind)
    TyToCtx-⨯ zero = []
    TyToCtx-⨯ (suc n) = TyToCtx-⨯ n ,, kind Te

    infixl 8 _$$_
    pattern _$$_ a b = app a b



  {-

    mutual
      TermFromTerm-⨯-var : ∀{n} -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ var) -> 𝔽ʳ n
      TermFromTerm-⨯-var {zero} (getapp (meta (skip ())))
      TermFromTerm-⨯-var {zero} (getapp (meta (give ())))
      TermFromTerm-⨯-var {suc n} (suc tep te) = suc (TermFromTerm-⨯-var te)
      TermFromTerm-⨯-var {suc n} (zero te) = zero
      TermFromTerm-⨯-var {suc n} (getapp (meta (skip ())))
      TermFromTerm-⨯-var {suc n} (getapp (meta (give ())))

      TermFromTerm-⨯-var-⊥ : ∀{n α β} -> [] ⊩↓ (TyToCtx-⨯ n ⊢ (α ⇒ β) ◀ var) -> 𝟘-𝒰
      TermFromTerm-⨯-var-⊥ {suc n} (suc tep te) = TermFromTerm-⨯-var-⊥ te

      TermFromTerm-⨯-app-⊥ : ∀{n α₁ α₂ α₃ α₄ α₅ β} -> [] ⊩↓-app (TyToCtx-⨯ n ⊢ (α₁ ⇒ α₂ ⇒ α₃ ⇒ α₄ ⇒ α₅ ⇒ β) ◀ main) -> 𝟘-𝒰
      TermFromTerm-⨯-app-⊥ (app te x) = TermFromTerm-⨯-app-⊥ te
      TermFromTerm-⨯-app-⊥ (var te) = TermFromTerm-⨯-var-⊥ te
      TermFromTerm-⨯-app-⊥ (meta (skip ()))
      TermFromTerm-⨯-app-⊥ (meta (give ()))

      TermFromTerm-⨯-app : ∀{n} -> [] ⊩↓-app (TyToCtx-⨯ n ⊢ kind Te ◀ main) -> Λ.Term-λ n
      TermFromTerm-⨯-app (app (app (app (app (app te x₄) x₃) x₂) x₁) x) = 𝟘-rec (TermFromTerm-⨯-app-⊥ te)
      TermFromTerm-⨯-app (app (app (app (app (var te) x₃) x₂) x₁) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
      TermFromTerm-⨯-app (app (app (app (app (meta (skip ())) x₃) x₂) x₁) y)
      TermFromTerm-⨯-app (app (app (app (app (meta (give ())) x₃) x₂) x₁) y)
      TermFromTerm-⨯-app (app (app (app (var te) x₂) x₁) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
      TermFromTerm-⨯-app (app (app (app (con Rec-ℕ) (lam te-suc)) te-zero) te-v) = rec-ℕ (TermFromTerm-⨯ te-suc) (TermFromTerm-⨯ te-zero) (TermFromTerm-⨯ te-v)
      TermFromTerm-⨯-app (app (app (app (meta (skip ())) x₂) x₁) x)
      TermFromTerm-⨯-app (app (app (app (meta (give ())) x₂) x₁) x)
      TermFromTerm-⨯-app (app (app (var te) x₁) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
      TermFromTerm-⨯-app (app (app (con App) x) y) = app (TermFromTerm-⨯ x) (TermFromTerm-⨯ y)
      TermFromTerm-⨯-app (app (app (meta (skip ())) x₁) x)
      TermFromTerm-⨯-app (app (app (meta (give ())) x₁) x)
      TermFromTerm-⨯-app (app (var te) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
      TermFromTerm-⨯-app (app (con Lam) (lam x)) = lam (TermFromTerm-⨯ x)
      TermFromTerm-⨯-app (app (con Suc) x) = suc (TermFromTerm-⨯ x)
      TermFromTerm-⨯-app (app (meta (skip ())) x)
      TermFromTerm-⨯-app (app (meta (give ())) x)
      TermFromTerm-⨯-app (var x) = var (TermFromTerm-⨯-var x)
      TermFromTerm-⨯-app (con Zero) = zero
      TermFromTerm-⨯-app (meta (skip ()))
      TermFromTerm-⨯-app (meta (give ()))

      TermFromTerm-⨯ : ∀{n} -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ main) -> Λ.Term-λ n
      TermFromTerm-⨯ (getapp x) = TermFromTerm-⨯-app x


  {-

    TermToTerm-⨯-var : {n : ℕ} -> 𝔽ʳ n -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ var)
    TermToTerm-⨯-var zero = zero (getapp (meta (skip varzero)))
    TermToTerm-⨯-var (suc i) = suc (getapp (meta (skip varsuc))) (TermToTerm-⨯-var i)

    TermToTerm-⨯ : ∀{n} -> Λ.Term-λ n -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ main)
    TermToTerm-⨯ (app te te2) = getapp ((con App) $$ (TermToTerm-⨯ te) $$ (TermToTerm-⨯ te2))
    TermToTerm-⨯ (lam te) = getapp ((con Lam) $$ (lam (TermToTerm-⨯ te)))
    TermToTerm-⨯ (var x) = getapp (var (TermToTerm-⨯-var x))
    TermToTerm-⨯ (zero) = getapp (con Zero)
    TermToTerm-⨯ (suc te) = getapp $ (con Suc) $$ (TermToTerm-⨯ te)
    TermToTerm-⨯ (rec-ℕ te-suc te-zero v) = getapp $ con Rec-ℕ $$ (lam (TermToTerm-⨯ te-suc)) $$ TermToTerm-⨯ te-zero $$ TermToTerm-⨯ v

    iso-left-var : ∀{n} -> (i : 𝔽ʳ n) -> TermFromTerm-⨯-var (TermToTerm-⨯-var i) ≡ i
    iso-left-var {.(suc _)} zero = refl
    iso-left-var {.(suc _)} (suc i) = λ k -> suc (iso-left-var i k)

    iso-left : ∀{n} -> (te : Term-λ n) -> TermFromTerm-⨯ (TermToTerm-⨯ te) ≡ te
    iso-left (te $$ te2) = λ i -> iso-left te i $$ iso-left te2 i
    iso-left (lam te) = λ i -> lam (iso-left te i)
    iso-left (var x) = λ k -> var (iso-left-var x k)
    iso-left zero = refl
    iso-left (suc te) = cong suc (iso-left te)
    iso-left (rec-ℕ te te1 te2) = λ i -> rec-ℕ (iso-left te i) (iso-left te1 i) (iso-left te2 i)


    ω : Term-λ 0
    ω = app (lam (app (var zero) (var zero))) (lam (app (var zero) (var zero)))




    -- TermFromTerm-⨯ (MTC.var t) = {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.var t) t₁) = {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.con Lam) t₁) = lam {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.lam t) t₁) = {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.app t t₂) t₁) = {!!}
    -- TermFromTerm-⨯ (MTC.var (MTC.meta ()))
    -- TermFromTerm-⨯ (MTC.app (MTC.var (MTC.meta ())) t₁)
    -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.var t)) t₁) = {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.app (MTC.var t) t₂)) t₁) = {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.app (MTC.lam t) t₂)) t₁) = {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.app (MTC.app t t₃) t₂)) t₁) = {!!}
    -- TermFromTerm-⨯ (MTC.app (MTC.app t t₂) t₁) = {!!}

  -}
  -}

-}
