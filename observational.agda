{-# OPTIONS --prop --rewriting --lossy-unification --type-in-type #-}

{- Cheeky type-in-type because I have only one universe level for now -}

open import Agda.Primitive
open import lib
open import setoids
open import typeformers
open import views
open import fibrancy
open import cwf
open import nat

{- In this file we define an observational equality for our CwF. It supports
   - reflexivity, symmetry, transitivity
   - function application
   - type-casting with cast-on-refl
   - function extensionality, UIP, proposition extensionality
   Everything is definitionally stable under substitution
-}

{- Small equality type with reflexivity, symmetry, transitivity, function application -}

Idₚ : {Γ : Con} (A : Ty Γ) (a : Tm Γ A) (b : Tm Γ A) → Ty Γ
Idₚ A a b .m-el γ = mkU (obseq-El (setoidApp A γ) (setoidApp A γ) (tmApp A a γ) (tmApp A b γ)) (cEmb _) (c₂Emb _) (c₃Emb _)
Idₚ {Γ} A a b .m-rel γ₀ γ₁ γe =
  mkLift₁
    (mkΣ 
      (λ e → let
               a1b0 : obseq-El (setoidApp A γ₁) (setoidApp A γ₀) (tmApp A a γ₁) (tmApp A b γ₀)
               a1b0 = obseq-trans (setoidApp A γ₀) (setoidApp A γ₀) (obseq-reflU (setoidApp A γ₀)) (setoidApp A γ₁) (tmApp A a γ₀)
                                  (tmApp A b γ₀) (tmApp A a γ₁) e (obseq-sym (setoidApp A γ₀) (setoidApp A γ₁) (tmApp A a γ₀) (tmApp A a γ₁) (tmAppEq A a γe))
             in obseq-trans (setoidApp A γ₀) (setoidApp A γ₁) (setoidAppEq A γ₀ γ₁ γe) (setoidApp A γ₁)
                            (tmApp A b γ₀) (tmApp A b γ₁) (tmApp A a γ₁) (tmAppEq A b γe) a1b0)
      (λ e → let
               a1b0 : obseq-El (setoidApp A γ₀) (setoidApp A γ₁) (tmApp A a γ₀) (tmApp A b γ₁)
               a1b0 = obseq-trans (setoidApp A γ₁) (setoidApp A γ₁) (obseq-reflU (setoidApp A γ₁)) (setoidApp A γ₀) (tmApp A a γ₁)
                                  (tmApp A b γ₁) (tmApp A a γ₀) e (tmAppEq A a γe)
             in obseq-trans (setoidApp A γ₁) (setoidApp A γ₀) (obseq-symU (setoidApp A γ₀) (setoidApp A γ₁) (setoidAppEq A γ₀ γ₁ γe)) (setoidApp A γ₀)
                            (tmApp A b γ₁) (tmApp A b γ₀) (tmApp A a γ₀) (obseq-sym (setoidApp A γ₀) (setoidApp A γ₁) (tmApp A b γ₀) (tmApp A b γ₁) (tmAppEq A b γe)) a1b0))
Idₚ A a b .m-refl = λ γ → tt₁

Id[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (a : Tm Γ A) (b : Tm Γ A) → (Idₚ A a b) [ σ ]ᵀ ≡ Idₚ (A [ σ ]ᵀ) (a [ σ ]ᵗ) (b [ σ ]ᵗ)
Id[] σ A a b = refl -- holds definitionally

reflₚ : {Γ : Con} (A : Ty Γ) (a : Tm Γ A) → Tm Γ (Idₚ A a a)
reflₚ A a .t-el γ = obseq-refl (setoidApp A γ) (tmApp A a γ)
reflₚ A a .t-rel γ₀ γ₁ e = ★
reflₚ A a .t-refl γ = tt

refl[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (a : Tm Γ A) → (reflₚ A a) [ σ ]ᵗ ≡ reflₚ (A [ σ ]ᵀ) (a [ σ ]ᵗ)
refl[] σ A a = refl -- holds definitionally

symₚ : {Γ : Con} (A : Ty Γ) (a b : Tm Γ A) (e : Tm Γ (Idₚ A a b)) → Tm Γ (Idₚ A b a)
symₚ A a b e .t-el γ = obseq-sym (setoidApp A γ) (setoidApp A γ) (tmApp A a γ) (tmApp A b γ) (tmApp (Idₚ A a b) e γ .p-el)
symₚ A a b e .t-rel γ₀ γ₁ γe = ★
symₚ A a b e .t-refl γ = tt

sym[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (a b : Tm Γ A) (e : Tm Γ (Idₚ A a b))
      → (symₚ A a b e) [ σ ]ᵗ ≡ symₚ (A [ σ ]ᵀ) (a [ σ ]ᵗ) (b [ σ ]ᵗ) (e [ σ ]ᵗ)
sym[] σ A a b e = refl -- holds definitionally

transₚ : {Γ : Con} (A : Ty Γ) (a b c : Tm Γ A) (e : Tm Γ (Idₚ A a b)) (f : Tm Γ (Idₚ A b c)) → Tm Γ (Idₚ A a c)
transₚ A a b c e f .t-el γ = obseq-trans (setoidApp A γ) (setoidApp A γ) (obseq-reflU (setoidApp A γ)) (setoidApp A γ)
                                         (tmApp A b γ) (tmApp A c γ) (tmApp A a γ) (tmApp (Idₚ A b c) f γ .p-el) (tmApp (Idₚ A a b) e γ .p-el)
transₚ A a b c e f .t-rel γ₀ γ₁ γe = ★
transₚ A a b c e f .t-refl γ = tt

trans[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (a b c : Tm Γ A) (e : Tm Γ (Idₚ A a b)) (f : Tm Γ (Idₚ A b c))
        → (transₚ A a b c e f) [ σ ]ᵗ ≡ transₚ (A [ σ ]ᵀ) (a [ σ ]ᵗ) (b [ σ ]ᵗ) (c [ σ ]ᵗ) (e [ σ ]ᵗ) (f [ σ ]ᵗ)
trans[] σ A a b c e f = refl -- holds definitionally

apₚ : {Γ : Con} (A B : Ty Γ) (f : Tm Γ (Πₚ A (B [ wk A ]ᵀ))) (a b : Tm Γ A) (e : Tm Γ (Idₚ A a b))
    → Tm Γ (Idₚ B (appₚ A (B [ wk A ]ᵀ) f a) (appₚ A (B [ wk A ]ᵀ) f b))
apₚ A B f a b e .t-el γ = obseq-refl (setoidApp (Πₚ A (B [ wk A ]ᵀ)) γ) (tmApp (Πₚ A (B [ wk A ]ᵀ)) f γ) (tmApp A a γ) (tmApp A b γ) (tmApp (Idₚ A a b) e γ .p-el)
apₚ A B f a b e .t-rel γ₀ γ₁ e₁ = ★
apₚ A B f a b e .t-refl γ = tt

ap[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A B : Ty Γ) (f : Tm Γ (Πₚ A (B [ wk A ]ᵀ))) (a b : Tm Γ A) (e : Tm Γ (Idₚ A a b))
     → (apₚ A B f a b e) [ σ ]ᵗ ≡ apₚ (A [ σ ]ᵀ) (B [ σ ]ᵀ) (f [ σ ]ᵗ) (a [ σ ]ᵗ) (b [ σ ]ᵗ) (e [ σ ]ᵗ)
ap[] σ A B f a b e = refl -- holds definitionally

{- Large equality type (for now, we can pretend that it is a small type thanks to type-in-type) -}

IdUₚ : {Γ : Con} (A B : Ty Γ) → Ty Γ
IdUₚ A B .m-el γ = mkU (SetoidEq (setoidApp A γ) (setoidApp B γ)) (cEmb _) (c₂Emb _) (c₃Emb _)
IdUₚ A B .m-rel γ₀ γ₁ γe =
  mkLift₁
    (mkΣ
      (λ e → let
               A0B1 : SetoidEq (setoidApp A γ₀) (setoidApp B γ₁)
               A0B1 = obseq-transU (setoidApp B γ₀) (setoidApp B γ₁) (setoidApp A γ₀) (setoidAppEq B γ₀ γ₁ γe) e
             in obseq-transU (setoidApp A γ₀) (setoidApp B γ₁) (setoidApp A γ₁)
                             A0B1 (obseq-symU (setoidApp A γ₀) (setoidApp A γ₁) (setoidAppEq A γ₀ γ₁ γe)))
      (λ e → let
               A0B1 : SetoidEq (setoidApp A γ₁) (setoidApp B γ₀)
               A0B1 = obseq-transU (setoidApp B γ₁) (setoidApp B γ₀) (setoidApp A γ₁) (obseq-symU (setoidApp B γ₀) (setoidApp B γ₁) (setoidAppEq B γ₀ γ₁ γe)) e
             in obseq-transU (setoidApp A γ₁) (setoidApp B γ₀) (setoidApp A γ₀)
                             A0B1 (setoidAppEq A γ₀ γ₁ γe)))
IdUₚ A B .m-refl γ = tt₁

IdU[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A B : Ty Γ) → (IdUₚ A B) [ σ ]ᵀ ≡ IdUₚ (A [ σ ]ᵀ) (B [ σ ]ᵀ)
IdU[] σ A B = refl -- holds definitionally

{- Type casting with cast-on-refl equality -}

castₚ : {Γ : Con} (A B : Ty Γ) (e : Tm Γ (IdUₚ A B)) (t : Tm Γ A) → Tm Γ B
castₚ A B e t .t-el γ = cast-el (setoidApp A γ) (setoidApp B γ) (tmApp (IdUₚ A B) e γ .p-el) (tmApp A t γ)
castₚ A B e t .t-rel γ₀ γ₁ γe = cast-rel (setoidApp A γ₀) (setoidApp A γ₁) (setoidAppEq A γ₀ γ₁ γe) (setoidApp B γ₀) (setoidApp B γ₁) (setoidAppEq B γ₀ γ₁ γe) (tmApp (IdUₚ A B) e γ₀ .p-el) (tmApp (IdUₚ A B) e γ₁ .p-el) (tmApp A t γ₀) (tmApp A t γ₁) (tmAppEq A t γe)
castₚ A B e t .t-refl γ = cast-refl (setoidApp A γ) (setoidApp B γ) (tmApp (IdUₚ A B) e γ .p-el) (tmApp A t γ)

cast[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A B : Ty Γ) (e : Tm Γ (IdUₚ A B)) (t : Tm Γ A)
       → (castₚ A B e t) [ σ ]ᵗ ≡ castₚ (A [ σ ]ᵀ) (B [ σ ]ᵀ) (e [ σ ]ᵗ) (t [ σ ]ᵗ)
cast[] σ A B e t = refl -- holds definitionally

cast-eqₚ : {Γ : Con} (A : Ty Γ) (e : Tm Γ (IdUₚ A A)) (t : Tm Γ A) → Tm Γ (Idₚ A t (castₚ A A e t))
cast-eqₚ A e t .t-el γ = cast-eq (setoidApp A γ) (setoidApp A γ) (tmApp (IdUₚ A A) e γ .p-el) (tmApp A t γ)
cast-eqₚ A e t .t-rel γ₀ γ₁ e₁ = ★
cast-eqₚ A e t .t-refl γ = tt

cast-eq[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A B : Ty Γ) (e : Tm Γ (IdUₚ A A)) (t : Tm Γ A)
          → (cast-eqₚ A e t) [ σ ]ᵗ ≡ cast-eqₚ (A [ σ ]ᵀ) (e [ σ ]ᵗ) (t [ σ ]ᵗ)
cast-eq[] σ A B e t = refl -- holds definitionally

{- Function extensionality (only for nondependent functions for now) -}

funextₚ : {Γ : Con} (A B : Ty Γ) (f g : Tm Γ (Πₚ A (B [ wk A ]ᵀ)))
          (e : Tm Γ (Πₚ A (Idₚ (B [ wk A ]ᵀ) (appₚ (A [ wk A ]ᵀ) (B [ wk A ∘ wk (A [ wk A ]ᵀ) ]ᵀ) (f [ wk A ]ᵗ) (var0 A)) (appₚ (A [ wk A ]ᵀ) (B [ wk A ∘ wk (A [ wk A ]ᵀ) ]ᵀ) (g [ wk A ]ᵗ) (var0 A)))))
        → Tm Γ (Idₚ (Πₚ A (B [ wk A ]ᵀ)) f g)
funextₚ A B f g e .t-el γ a b eab =
  obseq-trans (setoidApp B γ) (setoidApp B γ) (obseq-reflU (setoidApp B γ)) (setoidApp B γ)
              (Πᵤ-app (setoidApp A γ) (partialApp U A (B [ wk A ]ᵀ) γ) (tmApp (Πₚ A (B [ wk A ]ᵀ)) g γ) a)
              (Πᵤ-app (setoidApp A γ) (partialApp U A (B [ wk A ]ᵀ) γ) (tmApp (Πₚ A (B [ wk A ]ᵀ)) g γ) b)
              (Πᵤ-app (setoidApp A γ) (partialApp U A (B [ wk A ]ᵀ) γ) (tmApp (Πₚ A (B [ wk A ]ᵀ)) f γ) a)
              (obseq-refl (setoidApp (Πₚ A (B [ wk A ]ᵀ)) γ) (tmApp (Πₚ A (B [ wk A ]ᵀ)) g γ) a b eab)
              (tmApp (Πₚ A (Idₚ (B [ wk A ]ᵀ) (appₚ (A [ wk A ]ᵀ) (B [ wk A ∘ wk (A [ wk A ]ᵀ) ]ᵀ) (f [ wk A ]ᵗ) (var0 A)) (appₚ (A [ wk A ]ᵀ) (B [ wk A ∘ wk (A [ wk A ]ᵀ) ]ᵀ) (g [ wk A ]ᵗ) (var0 A)))) e γ .p-el a)
funextₚ A B f g e .t-rel γ₀ γ₁ e₁ = ★
funextₚ A B f g e .t-refl γ = tt

funext[] : {Δ Γ : Con} (σ : Sub Δ Γ) (A B : Ty Γ) (f g : Tm Γ (Πₚ A (B [ wk A ]ᵀ)))
           (e : Tm Γ (Πₚ A (Idₚ (B [ wk A ]ᵀ) (appₚ (A [ wk A ]ᵀ) (B [ wk A ∘ wk (A [ wk A ]ᵀ) ]ᵀ) (f [ wk A ]ᵗ) (var0 A)) (appₚ (A [ wk A ]ᵀ) (B [ wk A ∘ wk (A [ wk A ]ᵀ) ]ᵀ) (g [ wk A ]ᵗ) (var0 A)))))
         → (funextₚ A B f g e) [ σ ]ᵗ ≡ funextₚ (A [ σ ]ᵀ) (B [ σ ]ᵀ) (f [ σ ]ᵗ) (g [ σ ]ᵗ) (e [ σ ]ᵗ)
funext[] σ A B f g e = refl -- holds definitionally
