{-
  case (γ Γ te) of
  {!!}
  continue₀ where

  continue₀ : InitialCtxTypingInstance Γ te -> TypingDecision Γ (slet te se)
  continue₀ ((νs₀ₐ / νs₀ₓ ⊩ Γ₀ , αᵇ₀ , Γ<Γ₀ , Γ₀⊢αᵇ₀), Ω₀) = result
    where

      -- once we have typechecked te, we know that νs₀ₓ are the
      -- variables over which the type αᵇ₀ is quantified
      -- thus the context in which we typecheck `se` is the following
      α₀Γ₀ : ℒHMCtxFor (νs₀ₓ ∷' Q) νs₀ₐ
      α₀Γ₀ = αᵇ₀ ∷ Γ₀

      σᵃᵤ₀ = fst Γ<Γ₀

      result = case (γ α₀Γ₀ se) of
        {!!}
        continue₁ where

        continue₁ : InitialCtxTypingInstance (α₀Γ₀) se -> TypingDecision Γ (slet te se)
        continue₁ ((νs₁ₐ / νs₁ₓ ⊩ (α₁ ∷ Γ₁) , βᵇ₁ , α₀Γ₀<α₁Γ₁ , α₁Γ₁⊢βᵇ₁), Ω₁) = right (𝑇 , isInitial:𝑇)
          where
            Γ₀<Γ₁ : Γ₀ <Γ Γ₁
            Γ₀<Γ₁ = tail-SomeℒHMCtx α₀Γ₀<α₁Γ₁

            σᵃ₀₁ = fst Γ₀<Γ₁

            α₁' : ℒHMType ⟨ νs₁ₐ ⊔ νs₁ₓ ⊔ νs₀ₓ ⟩
            α₁' = (α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂)

            lem-1a : αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ id ]⇂ ≡ α₁
            lem-1a = λ i -> split-Listᴰ² (α₀Γ₀<α₁Γ₁ .snd i) .fst

            lem-1b : Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ≡ Γ₁
            lem-1b = λ i -> split-Listᴰ² (α₀Γ₀<α₁Γ₁ .snd i) .snd

            Γ₁⊢α₁' : isTypedℒHM (νs₁ₐ ⊔ νs₁ₓ ⊔ νs₀ₓ ⊩ (_ , Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) ⊢ α₁') te
            Γ₁⊢α₁' = Γ₀⊢αᵇ₀
                      >> isTypedℒHM ((νs₀ₐ ⊔ νs₀ₓ) ⊩ Q , (Γ₀ ⇃[ ι₀ ]⇂ᶜ) ⊢ αᵇ₀) te <<
                      ⟪ §-isTypedℒHM.prop-4 σᵃ₀₁ id ⟫
                      >> isTypedℒHM (_ ⊩ Q , (Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ id ]⇂) te <<

                      ⟪ transp-isTypedℒHM (cong _⇃[ ι₀ ]⇂ᶜ lem-1b) lem-1a ⟫

                      >> isTypedℒHM (_ ⊩ Q , (Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₁ ) te <<

                      ⟪ §-isTypedℒHM.prop-4 ι₀ id ⟫

                      >> isTypedℒHM (_ ⊩ Q , (Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ) te <<

                      ⟪ transp-isTypedℒHM (functoriality-◆-⇃[]⇂-CtxFor) refl-≡ ⟫

                      >> isTypedℒHM (_ ⊩ Q , (Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) ⊢ α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ) te <<


            lem-2 : Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⇃[ ⟨ refl-≅ ⟩ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
            lem-2 = trans-Path (functoriality-id-⇃[]⇂-CtxFor) (sym-Path functoriality-◆-⇃[]⇂-CtxFor)

            isAb : isAbstr νs₀ₓ (Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) (Γ₁ ⇃[ ι₀ ]⇂ᶜ) α₁' (α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂)
            isAb = record { metasProof = refl-≅ ; ctxProof = lem-2 ; typeProof = functoriality-id-⇃[]⇂ }


            𝑇 : CtxTypingInstance Γ (slet te se)
            𝑇 = νs₁ₐ / νs₁ₓ ⊩ Γ₁ , βᵇ₁ , Γ<Γ₀ ⟡ Γ₀<Γ₁ , (slet isAb Γ₁⊢α₁' α₁Γ₁⊢βᵇ₁)

            isInitial:𝑇 : ∀(𝑆 : CtxTypingInstance Γ (slet te se)) -> 𝑇 <TI 𝑆
            isInitial:𝑇 (νs₃ₐ / νs₃ₓ ⊩ Γ₃ , β₃ , Γ<Γ₃ , slet {μs = νs₂} {κs = νs₃ₓ₊} {Γ = Γ₂} {α = α₂} {α' = α₃}  isAb₂ Γ₂⊢α₂ α₃Γ₃⊢β₃) =
              record { tiSubₐ = σᵃ₁₃ ; tiSubₓ = σˣ₁₃ ; typProof = lem-30 ; subProof = lem-40 }
              where
                σ₂₃₊ : νs₂ ≅ νs₃ₐ ⊔ νs₃ₓ ⊔ νs₃ₓ₊
                σ₂₃₊ = metasProof isAb₂

                -- lem-10 : isTypedℒHM (νs₃ₐ ⊔ νs₃ₓ ⊔ νs₃ₓ₊ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₃) te
                -- lem-10 = {!!}

                あ : ((νs₃ₐ ⊔ νs₃ₓ) ⊔ νs₃ₓ₊) ≅ (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))
                あ = let x = assoc-l-⊔-ℒHMTypes {a = νs₃ₐ} {b = νs₃ₓ} {c = νs₃ₓ₊} in x

                α₃' : ℒHMType ⟨(νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))⟩
                α₃' = α₃ ⇃[ ⟨ あ ⟩ ]⇂

                lem-11 : isTypedℒHM (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₃') te
                lem-11 = Γ₂⊢α₂
                         >> isTypedℒHMᵈ (νs₂ ⊩ Q , Γ₂ ⊢ α₂) te <<
                         ⟪ §-isTypedℒHM.prop-2 ⟨ σ₂₃₊ ⟩ ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂ᶜ ⊢ α₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂) te <<
                         ⟪ transp-isTypedℒHM (trans-Path (ctxProof isAb₂) functoriality-◆-⇃[]⇂-CtxFor) (typeProof isAb₂) ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⊢ α₃) te <<
                         ⟪ §-isTypedℒHM.prop-2 ⟨ あ ⟩ ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⇃[ ⟨ あ ⟩ ]⇂ᶜ ⊢ α₃ ⇃[ ⟨ あ ⟩ ]⇂) te <<
                         ⟪ transp-isTypedℒHM (trans-Path (functoriality-◆-⇃[]⇂-CtxFor) (Γ₃ ⇃[≀ {!!} ≀]⇂ᶜ)) refl-≡ ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te <<

                Ω₀R = Ω₀ ((νs₃ₐ) / (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ , α₃' , Γ<Γ₃ , lem-11)

                σᵃ₀₃ : νs₀ₐ ⟶ νs₃ₐ
                σᵃ₀₃ = tiSubₐ Ω₀R

                σˣ₀₃ : νs₀ₓ ⟶ νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊)
                σˣ₀₃ = tiSubₓ Ω₀R

                -- σˣ₀₃ : νs₀ₓ ⟶ (νs₃ₐ ⊔ νs₃ₓ) ⊔ νs₃ₓ₊
                -- σˣ₀₃ = σˣ₀₃ᵘ ◆ {!!}

                α₀' = αᵇ₀ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂

                lem-14 : ⦗ σᵃ₀₃ ◆ ι₀ ◆ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ∼ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹
                lem-14 = {!!}

                lem-15 : α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ≡ α₃
                lem-15 = {!!}

                lem-20 : isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₀ₓ ∷ Q) , ((α₀' ∷ Γ₃) ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se
                lem-20 = α₃Γ₃⊢β₃
                       >> isTypedℒHMᵈ ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₃ₓ₊ ∷ Q) , (α₃ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                       ⟪ transp-isTypedℒHM ((λ i -> lem-15 (~ i) ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ))) refl-≡ ⟫
                       >> isTypedℒHMᵈ ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₃ₓ₊ ∷ Q) , (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                       ⟪ {!!} ⟫
                       >> isTypedℒHMᵈ ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₀ₓ ∷ Q) , (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<

                α₀Γ₀<α₀'Γ₃ :  α₀Γ₀ <Γ (α₀' ∷ Γ₃)
                α₀Γ₀<α₀'Γ₃ = record { fst = σᵃ₀₃ ; snd = λ i -> α₀' ∷ ctxProofTI Ω₀R i }

                Ω₁R = Ω₁ (νs₃ₐ / νs₃ₓ ⊩ α₀' ∷ Γ₃ , β₃ , α₀Γ₀<α₀'Γ₃ , lem-20)

                σᵃ₁₃ : νs₁ₐ ⟶ νs₃ₐ
                σᵃ₁₃ = tiSubₐ Ω₁R

                σˣ₁₃ : νs₁ₓ ⟶ (νs₃ₐ ⊔ νs₃ₓ)
                σˣ₁₃ = tiSubₓ Ω₁R

                lem-30 : βᵇ₁ ⇃[ ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘ ]⇂ ≡ β₃
                lem-30 = let p1 = typProof Ω₁R in p1

                lem-40 : σᵃᵤ₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃ ∼ fst Γ<Γ₃
                lem-40 = σᵃᵤ₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃   ⟨ assoc-l-◆ ⟩-∼
                         σᵃᵤ₀ ◆ (σᵃ₀₁ ◆ σᵃ₁₃) ⟨ refl ◈ subProof Ω₁R ⟩-∼
                         σᵃᵤ₀ ◆ σᵃ₀₃          ⟨ subProof Ω₀R ⟩-∼
                         fst Γ<Γ₃             ∎

-}
