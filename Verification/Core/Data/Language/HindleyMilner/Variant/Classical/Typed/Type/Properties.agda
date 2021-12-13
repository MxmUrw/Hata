
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type.Properties where

open import Verification.Conventions hiding (ℕ ; _⊔_)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTermTerm.Signature


-- [Hide]

instance
  hasSplitEpiMonoFactorization:ℒHMTypes : hasSplitEpiMonoFactorization ℒHMTypes
  hasSplitEpiMonoFactorization:ℒHMTypes = {!!}

-- //


-- | We define substitutions of types.
--   for that we need some stuff.
--   We mostly ignore the concrete definition
--   of the category of type variables and
--   substitutions. Merely using its categorical
--   properties, in particular, that:
-- | - it has coproducts,
-- | - it has unification,
-- | - it has epi-mono factorization.
--
-- |: Nevertheless, we also do want to work
--    with concrete types, as defined in ...
--    The relation of the category with these
--    concrete types is given by the following few statements.

-- | First, the element in |ℒHMTypes| representing
--   a single type variable is given by:
st : ℒHMTypes
st = incl (incl tt)

-- | Next, given a type with type variables |μs|, we can consider it as a morphism
--   from |st| to |μs| in |ℒHMType|.
asArr : ∀{μs} -> ℒHMType ⟨ μs ⟩ -> (st ⟶ μs)
asArr t = ⧜subst (incl t)

-- | Also, given such a morphism, we can extract the
--   actual type from it.
fromArr : ∀{μs} -> (st ⟶ μs) -> ℒHMType ⟨ μs ⟩
fromArr (⧜subst (incl x)) = x

-- | This allows us to define:
abstract

  -- [Definition]
  -- | Let ... and a lot of stuff, then substitution is defined by:
  _⇃[_]⇂ : ∀{μs νs : ℒHMTypes} -> 𝒯⊔Term 𝒹 ⟨ μs ⟩ tt -> (μs ⟶ νs) -> 𝒯⊔Term 𝒹 ⟨ νs ⟩ tt
  _⇃[_]⇂ x f = fromArr (asArr x ◆ f)

  infixl 80 _⇃[_]⇂

  -- //

  -- [Hide]
  -- | Since substitution is abstract, we need a lemma for unwrapping the
  --   definition.

  -- the abstraction equality
  abstract-⇃[]⇂ : ∀{a b : ℒHMTypes} -> {τ : 𝒯⊔Term 𝒹 ⟨ a ⟩ tt} -> {σ : a ⟶ b}
                  -> fromArr (asArr τ ◆ σ) ≡ τ ⇃[ σ ]⇂
  abstract-⇃[]⇂ = refl-≡
  -- //

-- [Lemma]
-- | The substitution operation is functorial. That is,
-- | 1. Substituting the identity morphism does not change the type.
-- | 2. Substituting a composition of morphisms is the composition
--      of substitutions.

-- //

-- [Proof]
-- | To prove this, the definition of composition in |ℒHMTypes| has to be unwrapped,
--   in order deal with the |fromArr| and |asArr| terms as given in REF Definition.
--   But apart from that, it is done using the associativity and unitality of composition.
--   Which in turn ultimately derives from the similar proofs in Section REF.

-- //

-- [Definition]
-- | Instantiation and generic instantiation. Given a type scheme |τ : ℒHMType ⟨ μs ⊔ αs ⟩|,
--   with free type variables |μs| and generic type variables |αs|, we can consider substitutions
--   which only affect one kind of type variables:
-- | - A substitution |σ : μs ⟶ νs| which only affects the free type variables.
--     The type |τ' = τ ⇃[ σ ⇃⊔⇂ id ]⇂ : ℒHMType ⟨ μs ⊔ αs ⟩|, is called an /instance/ of the
--     type |τ|.
-- | - A substitution |σ : αs ⟶ μs ⊔ βs| which acts on the generic,bound variables |αs|,
--     replacing them by terms which might contain the free variables |μs|, as well as
--     elements of a list |βs| of new generic,bound variables.
--     The type |τ' = τ ⇃[ ⦗ ι₀ , σ ⦘ ]⇂| is called a /generic instance/ of |τ|.

-- //


-- [Hide]

isInjective:fromArr : ∀{a} {α β : st ⟶ a} -> fromArr α ≡ fromArr β -> α ≡ β
isInjective:fromArr {α = ⧜subst (incl α)} {β = ⧜subst (incl β)} p = λ i -> ⧜subst (incl (p i))


abstract
  unify-ℒHMTypes : ∀{a b : ℒHMTypes} -> (f g : a ⟶ b) -> (¬ hasCoequalizerCandidate (f , g)) +-𝒰 (hasCoequalizer f g)
  unify-ℒHMTypes f g = unify f g


-- //

-- [Hide]

  --------------------------------------
  -- is setoid hom
  _⇃[≀_≀]⇂ : ∀{a b : ℒHMTypes} -> (τ : ℒHMType ⟨ a ⟩) -> {f g : a ⟶ b}
                -> f ∼ g -> τ ⇃[ f ]⇂ ≡ τ ⇃[ g ]⇂
  _⇃[≀_≀]⇂ τ {f = f} {g} p = cong fromArr (≡-Str→≡ (refl-≣ ◈ p))

  --------------------------------------
  -- respects ◆

  module _ {a b c : ℒHMTypes} where
    abstract
      functoriality-◆-⇃[]⇂ : ∀{τ : ℒHMType ⟨ a ⟩} -> {f : a ⟶ b} -> {g : b ⟶ c}
                              -> τ ⇃[ f ]⇂ ⇃[ g ]⇂ ≡ τ ⇃[ f ◆ g ]⇂
      functoriality-◆-⇃[]⇂ {τ} {f} {g} = cong fromArr lem-0
        where

          --   Removing the abstraction. We switch over in two steps from the abstract
          --   to the non-abstract.
          lem-3a : (⧜subst (incl (fromArr (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 f))) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g)
                  ≡ (⧜subst (incl (fromArr (⧜subst (incl τ) ◆-⧜𝐒𝐮𝐛𝐬𝐭 f))) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g)
          lem-3a =
            let p-0 : (⧜subst (incl (fromArr (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 f))) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g)
                    ≡ (⧜subst (incl (fromArr (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 f))) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g)
                p-0 = sym-Path $ ≡-Str→≡ $ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭
                        {f = ⧜subst (incl (fromArr (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 f)))}
                        {g = g}

                p-1 : ((⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 f))
                    ≡ ((⧜subst (incl τ) ◆-⧜𝐒𝐮𝐛𝐬𝐭 f))
                p-1 = sym-Path $ ≡-Str→≡ $ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭
                        {f = (⧜subst (incl τ))}
                        {g = f}

            in trans-Path p-0 (cong (λ ξ -> ⧜subst (incl (fromArr ξ)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) p-1)

          --   With removed `abstract`, the terms are definitionally equal.
          lem-3 : (⧜subst (incl (fromArr (⧜subst (incl τ) ◆-⧜𝐒𝐮𝐛𝐬𝐭 f))) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ≡ (((asArr τ ◆-⧜𝐒𝐮𝐛𝐬𝐭 f)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g)
          lem-3 = refl-≡

          --   Recreating the abstraction.
          lem-3b : (((asArr τ ◆-⧜𝐒𝐮𝐛𝐬𝐭 f)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ≡ (((asArr τ ◆ f)) ◆ g)
          lem-3b =
            let p-0 : (asArr τ ◆-⧜𝐒𝐮𝐛𝐬𝐭 f) ≡ (asArr τ ◆ f)
                p-0 = ≡-Str→≡ $ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭
                                    {f = asArr τ}
                                    {g = f}

                p-1 : (((asArr τ ◆ f)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ≡ (((asArr τ ◆ f)) ◆ g)
                p-1 = ≡-Str→≡ $ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭
                                    {f = asArr τ ◆ f}
                                    {g = g}

            in trans-Path (cong (_◆-⧜𝐒𝐮𝐛𝐬𝐭 g) p-0) p-1

          --   The actual proof is by associativity.
          lem-2 : (((asArr τ 内◆-⧜𝐒𝐮𝐛𝐬𝐭 f)) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ≡ (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 (f 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g))
          lem-2 = ≡-Str→≡ assoc-l-◆

          --   With that we are done.
          lem-0 : (⧜subst (incl (fromArr (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 f))) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ≡ (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 (f 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g))
          lem-0 = trans-Path (trans-Path lem-3a lem-3b) (lem-2)


  -------------------------
  -- respects id

  module _ {a : ℒHMTypes} where
    abstract
      functoriality-id-⇃[]⇂ : ∀{τ : ℒHMType ⟨ a ⟩} -> τ ⇃[ id ]⇂ ≡ τ
      functoriality-id-⇃[]⇂ {τ} = lem-0
        where
          lem-0 : fromArr (⧜subst (incl τ) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 内id-⧜𝐒𝐮𝐛𝐬𝐭) ≡ τ
          lem-0 = cong fromArr (≡-Str→≡ (unit-r-◆ {f = (⧜subst (incl τ))}))

  module §-⇃[]⇂ where
    -------------------------
    -- preserves the constructors of 𝒹
    module _ {a b : ℒHMTypes} {σ : a ⟶ b} where
      abstract
        prop-1 : {α β : ℒHMType ⟨ a ⟩} -> (α ⇒ β) ⇃[ σ ]⇂ ≡ α ⇃[ σ ]⇂ ⇒ β ⇃[ σ ]⇂
        prop-1 {α} {β} = ≡-Str→≡ (lem-1 ∙-≣ sym-≣ lem-2)
          where
            lem-1 : fromArr (⧜subst (incl (α ⇒ β)) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 σ) ≣ fromArr (⧜subst (incl (α ⇒ β)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 σ)
            lem-1 = cong-Str fromArr (sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭)

            lem-2 : (fromArr (⧜subst (incl α) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 σ) ⇒ fromArr (⧜subst (incl β) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 σ))
                    ≣ (fromArr (⧜subst (incl α) ◆-⧜𝐒𝐮𝐛𝐬𝐭 σ) ⇒ fromArr (⧜subst (incl β) ◆-⧜𝐒𝐮𝐛𝐬𝐭 σ))
            lem-2 = cong₂-Str _⇒_
                     (cong-Str fromArr (sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭))
                     (cong-Str fromArr (sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭))

    -------------------------
    -- substituting single arrows get us the content of the arrow
    module _ {μs : ℒHMTypes} where
      abstract
        prop-2 : {α : ℒHMType ⟨ μs ⟩} -> (var incl) ⇃[ asArr α ]⇂ ≡ α
        prop-2 {α} =
          let
            lem-1 : (⧜subst (incl (var incl)) 内◆-⧜𝐒𝐮𝐛𝐬𝐭 ⧜subst (incl α))
                  ≣ (⧜subst (incl (var incl)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 ⧜subst (incl α))
            lem-1 = sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭

          in ≡-Str→≡ (cong-Str fromArr lem-1)

-- //
