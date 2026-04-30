{-# OPTIONS --prop --rewriting --lossy-unification #-}

open import Agda.Primitive
open import lib
open import setoids
open import typeformers
open import views
open import fibrancy
open import cwf
open import nat

{- In this file, we define propositional truncation, and we derive proofs of
   * the principle of countable choice (under no assumption)
   * the principle of definite description, a.k.a. unique choice (under the assumption of decidable equality) -}

{- Propositional truncation -}

TruncMorphism : SetoidMorphism U U
TruncMorphism .m-el A = mkU (SetoidPt (El A)) (cEmb _) (c₂Emb _) (c₃Emb _)
TruncMorphism .m-rel A B e = mkLift₁ (mkΣ (λ x → cast A B e x) (λ x → cast B A (obseq-symU A B e) x))
TruncMorphism .m-refl A = tt₁

Truncₚ : {Γ : Con} (A : Ty Γ) → Ty Γ
Truncₚ A .m-el γ = mkU (SetoidPt (El (setoidApp A γ))) (cEmb _) (c₂Emb _) (c₃Emb _)
Truncₚ A .m-rel γ₀ γ₁ γe = mkLift₁ (mkΣ (λ x → cast (setoidApp A γ₀) (setoidApp A γ₁) (setoidAppEq A γ₀ γ₁ γe) x) 
                                       (λ x → cast (setoidApp A γ₁) (setoidApp A γ₀) (obseq-symU (setoidApp A γ₀) (setoidApp A γ₁) (setoidAppEq A γ₀ γ₁ γe)) x))
Truncₚ A .m-refl γ = tt₁

Trunc[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) → (Truncₚ A) [ σ ]ᵀ ≡ Truncₚ (A [ σ ]ᵀ)
Trunc[] σ A = refl -- holds definitionally

{- Countable choice -}

Setoidℕeq→≡ : (n m : SetoidPt (El ℕᵤ)) (e : nateq (n .p-el) (m .p-el)) → n ≡ m
Setoidℕeq→≡ n m e with nateq→≡ e
...               | refl = SetoidPt-eq₂ (El ℕᵤ) (nateq-is-hProp (m .p-el) (m .p-el) _ (m .p-rel)) tt tt

ACℕ : (P : SetoidMorphism Setoidℕ U) (h : SetoidPt (El (Πᵤ SetoidℕU (TruncMorphism ∘ P)))) → SetoidPt (El (Πᵤ SetoidℕU P))
ACℕ P h .p-el n = h .p-el n .p-el
ACℕ P h .p-rel n m e =
  transp (λ m → El-eq (P .m-el n .U-inU) (P .m-el m .U-inU) (h .p-el n .p-el) (h .p-el m .p-el)) (Setoidℕeq→≡ n m e) (h .p-el n .p-rel)
ACℕ P h .p-refl n = h .p-el n .p-refl

ACℕₚ : {Γ : Con} (P : Ty (Γ ▹ ℕₚ)) (h : Tm Γ (Πₚ ℕₚ (Truncₚ P))) → Tm Γ (Truncₚ (Πₚ ℕₚ P))
ACℕₚ P h .t-el γ = ACℕ (partialApp U ℕₚ P γ) (tmApp (Πₚ ℕₚ (Truncₚ P)) h γ)
ACℕₚ P h .t-rel γ₀ γ₁ γe = ★
ACℕₚ P h .t-refl γ = tt

ACℕ[] : {Γ Δ : Con} (σ : Sub Δ Γ) (P : Ty (Γ ▹ ℕₚ)) (h : Tm Γ (Πₚ ℕₚ (Truncₚ P)))
      → (ACℕₚ P h) [ σ ]ᵗ ≡ ACℕₚ (P [ ↑ σ ℕₚ ]ᵀ) (h [ σ ]ᵗ)
ACℕ[] σ P h = refl -- holds definitionally
