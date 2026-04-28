{-# OPTIONS --prop --rewriting --lossy-unification #-}

open import Agda.Primitive
open import lib
open import setoids
open import typeformers
open import views
open import fibrancy
open import cwf

{- Natural numbers with large elimination -}

ℕₚ : {Γ : Con} → Ty Γ
ℕₚ {Γ} .m-el γ = mkU ℕ cℕ c₂ℕ c₃ℕ
ℕₚ {Γ} .m-rel γ₀ γ₁ γe = ★₁
ℕₚ {Γ} .m-refl γ = tt₁

ℕ[] : {Γ Δ : Con} (σ : Sub Δ Γ) → ℕₚ [ σ ]ᵀ ≡ ℕₚ
ℕ[] σ = refl -- holds definitionally

zeroₚ : {Γ : Con} → Tm Γ ℕₚ
zeroₚ {Γ} .t-el γ = zero
zeroₚ {Γ} .t-rel γ₀ γ₁ γe = nateq-zero
zeroₚ {Γ} .t-refl γ = tt

zero[] : {Γ Δ : Con} (σ : Sub Δ Γ) → zeroₚ [ σ ]ᵗ ≡ zeroₚ 
zero[] σ = refl -- holds definitionally

sucₚ : {Γ : Con} (n : Tm Γ ℕₚ) → Tm Γ ℕₚ
sucₚ n .t-el γ = suc (n .t-el γ)
sucₚ n .t-rel γ₀ γ₁ γe = nateq-suc (n .t-rel γ₀ γ₁ γe)
sucₚ n .t-refl γ = tt

suc[] : {Γ Δ : Con} (σ : Sub Δ Γ) (n : Tm Γ ℕₚ) → (sucₚ n) [ σ ]ᵗ ≡ sucₚ (n [ σ ]ᵗ)
suc[] σ n = refl -- holds definitionally

{- Now for the eliminator (warning: the proof term is somewhat unpleasant) -}

Setoid0 : SetoidPt Setoidℕ
Setoid0 .p-el = zero
Setoid0 .p-rel = nateq-zero
Setoid0 .p-refl = tt

SetoidℕU : SetoidPt U
SetoidℕU .p-el = mkU ℕ cℕ c₂ℕ c₃ℕ
SetoidℕU .p-rel = ★₁
SetoidℕU .p-refl = tt₁

SetoidSuc : (n : SetoidPt Setoidℕ) → SetoidPt Setoidℕ
SetoidSuc n .p-el = suc (n .p-el)
SetoidSuc n .p-rel = nateq-suc (n .p-rel)
SetoidSuc n .p-refl = tt

SetoidSucMorphism : SetoidMorphism Setoidℕ Setoidℕ
SetoidSucMorphism .m-el n = suc (n .p-el)
SetoidSucMorphism .m-rel n m e = nateq-suc e
SetoidSucMorphism .m-refl n = tt

mutual
  ℕrec-el : (P : SetoidMorphism Setoidℕ U) (Pz : SetoidPt (El (setoidApp P Setoid0)))
            (Ps : SetoidPt (El (Πᵤ SetoidℕU (Πₚ P ((P ∘ SetoidSucMorphism) ∘ (wk P))))))
            (n : SetoidPt Setoidℕ) → (El (setoidApp P n)) .s-el
  ℕrec-el P Pz Ps (mkPt zero nateq-zero nr) = Pz .p-el
  ℕrec-el P Pz Ps (mkPt (suc n) (nateq-suc ne) nr) =
    Πᵤ-app (setoidApp P (mkPt n ne nr)) (partialApp {A = SetoidℕU} U P ((P ∘ SetoidSucMorphism) ∘ (wk P)) (mkPt n ne nr))
           (Πᵤ-app SetoidℕU (Πₚ P ((P ∘ SetoidSucMorphism) ∘ (wk P))) Ps (mkPt n ne nr))
           (mkPt (ℕrec-el P Pz Ps (mkPt n ne nr))
                 (ℕrec-rel P P (P .m-rel) Pz Pz (Pz .p-rel) Ps Ps (Ps .p-rel) (mkPt n ne nr) (mkPt n ne nr) ne)
                 (ℕrec-refl P Pz Ps (mkPt n ne nr))) .p-el

  ℕrec-rel : (P₀ P₁ : SetoidMorphism Setoidℕ U)
             (Pe : (n m : SetoidPt Setoidℕ) (eab : obseq-El SetoidℕU SetoidℕU n m) → SetoidEq (setoidApp P₀ n) (setoidApp P₁ m))
             (Pz₀ : SetoidPt (El (setoidApp P₀ Setoid0))) (Pz₁ : SetoidPt (El (setoidApp P₁ Setoid0)))
             (Pze : obseq-El (setoidApp P₀ Setoid0) (setoidApp P₁ Setoid0) Pz₀ Pz₁)
             (Ps₀ : SetoidPt (El (Πᵤ SetoidℕU (Πₚ P₀ ((P₀ ∘ SetoidSucMorphism) ∘ (wk P₀))))))
             (Ps₁ : SetoidPt (El (Πᵤ SetoidℕU (Πₚ P₁ ((P₁ ∘ SetoidSucMorphism) ∘ (wk P₁))))))
             (Pse : obseq-El (Πᵤ SetoidℕU (Πₚ P₀ ((P₀ ∘ SetoidSucMorphism) ∘ (wk P₀)))) (Πᵤ SetoidℕU (Πₚ P₁ ((P₁ ∘ SetoidSucMorphism) ∘ (wk P₁)))) Ps₀ Ps₁)
             (n₀ : SetoidPt (El SetoidℕU)) (n₁ : SetoidPt (El SetoidℕU)) (ne : obseq-El SetoidℕU SetoidℕU n₀ n₁)
             → El-eq (setoidApp P₀ n₀ .p-el .U-inU) (setoidApp P₁ n₁ .p-el .U-inU) (ℕrec-el P₀ Pz₀ Ps₀ n₀) (ℕrec-el P₁ Pz₁ Ps₁ n₁)
  ℕrec-rel P₀ P₁ Pe Pz₀ Pz₁ Pze Ps₀ Ps₁ Pse (mkPt zero nateq-zero nr) (mkPt zero nateq-zero mr) nateq-zero = Pze
  ℕrec-rel P₀ P₁ Pe Pz₀ Pz₁ Pze Ps₀ Ps₁ Pse (mkPt (suc n) (nateq-suc ne) nr) (mkPt (suc m) (nateq-suc me) mr) (nateq-suc e) =
    Πᵤ-app-rel
      (setoidApp P₀ (mkPt n ne nr))
      (setoidApp P₁ (mkPt m me mr))
      (Pe (mkPt n ne nr) (mkPt m me mr) e)
      (partialApp {A = SetoidℕU} U P₀ ((P₀ ∘ SetoidSucMorphism) ∘ (wk P₀)) (mkPt n ne nr))
      (partialApp {A = SetoidℕU} U P₁ ((P₁ ∘ SetoidSucMorphism) ∘ (wk P₁)) (mkPt m me mr))
      (λ p₀ p₁ pe → Pe (SetoidSuc (mkPt n ne nr)) (SetoidSuc (mkPt m me mr)) (nateq-suc e))
      (Πᵤ-app SetoidℕU (Πₚ P₀ ((P₀ ∘ SetoidSucMorphism) ∘ (wk P₀))) Ps₀ (mkPt n ne nr))
      (Πᵤ-app SetoidℕU (Πₚ P₁ ((P₁ ∘ SetoidSucMorphism) ∘ (wk P₁))) Ps₁ (mkPt m me mr))
      (Πᵤ-app-rel SetoidℕU SetoidℕU ★₁ (Πₚ P₀ ((P₀ ∘ SetoidSucMorphism) ∘ (wk P₀))) (Πₚ P₁ ((P₁ ∘ SetoidSucMorphism) ∘ (wk P₁)))
        (λ n m e → mkΣ (Pe n m e) (λ p₀ p₁ pe → Pe (SetoidSuc n) (SetoidSuc m) (nateq-suc e))) Ps₀ Ps₁ Pse (mkPt n ne nr) (mkPt m me mr) e)
      (mkPt
        (ℕrec-el P₀ Pz₀ Ps₀ (mkPt n ne nr))
        (ℕrec-rel P₀ P₀ (P₀ .m-rel) Pz₀ Pz₀ (Pz₀ .p-rel) Ps₀ Ps₀ (Ps₀ .p-rel) (mkPt n ne nr) (mkPt n ne nr) ne)
        (ℕrec-refl P₀ Pz₀ Ps₀ (mkPt n ne nr)))
      (mkPt 
        (ℕrec-el P₁ Pz₁ Ps₁ (mkPt m me mr))
        (ℕrec-rel P₁ P₁ (P₁ .m-rel) Pz₁ Pz₁ (Pz₁ .p-rel) Ps₁ Ps₁ (Ps₁ .p-rel) (mkPt m me mr) (mkPt m me mr) me)
        (ℕrec-refl P₁ Pz₁ Ps₁ (mkPt m me mr)))
      (ℕrec-rel P₀ P₁ Pe Pz₀ Pz₁ Pze Ps₀ Ps₁ Pse (mkPt n ne nr) (mkPt m me mr) e)

  ℕrec-refl : (P : SetoidMorphism Setoidℕ U) (Pz : SetoidPt (El (setoidApp P Setoid0)))
              (Ps : SetoidPt (El (Πᵤ SetoidℕU (Πₚ P ((P ∘ SetoidSucMorphism) ∘ (wk P))))))
              (n : SetoidPt Setoidℕ) → El-refl (setoidApp P n .p-el .U-inU₂) (ℕrec-el P Pz Ps n) (ℕrec-rel P P (P .m-rel) Pz Pz (Pz .p-rel) Ps Ps (Ps .p-rel) n n (n .p-rel))
  ℕrec-refl P Pz Ps (mkPt zero nateq-zero nr) = Pz .p-refl
  ℕrec-refl P Pz Ps (mkPt (suc n) (nateq-suc ne) nr) =
    Πᵤ-app-refl (setoidApp P (mkPt n ne nr)) (partialApp {A = SetoidℕU} U P ((P ∘ SetoidSucMorphism) ∘ (wk P)) (mkPt n ne nr))
                (Πᵤ-app SetoidℕU (Πₚ P ((P ∘ SetoidSucMorphism) ∘ (wk P))) Ps (mkPt n ne nr))
                (mkPt
                  (ℕrec-el P Pz Ps (mkPt n ne nr))
                  (ℕrec-rel P P (P .m-rel) Pz Pz (Pz .p-rel) Ps Ps (Ps .p-rel) (mkPt n ne nr) (mkPt n ne nr) ne)
                  (ℕrec-refl P Pz Ps (mkPt n ne nr)))

sucSub : (Γ : Con) → Sub (Γ ▹ ℕₚ) (Γ ▹ ℕₚ)
sucSub Γ = pair (wk ℕₚ) (sucₚ (var0 {Γ} ℕₚ))

ℕrec : {Γ : Con} (P : Ty (Γ ▹ ℕₚ)) (Pz : Tm Γ (P [ sg ℕₚ zeroₚ ]ᵀ)) (Ps : Tm Γ (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))))
       (n : Tm Γ ℕₚ) → Tm Γ (P [ sg ℕₚ n ]ᵀ)
ℕrec {Γ} P Pz Ps n .t-el γ =
  ℕrec-el (partialApp U ℕₚ P γ) (tmApp (P [ sg ℕₚ zeroₚ ]ᵀ) Pz γ) (tmApp (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))) Ps γ) (tmApp ℕₚ n γ)
ℕrec {Γ} P Pz Ps n .t-rel γ₀ γ₁ γe =
  ℕrec-rel
    (partialApp U ℕₚ P γ₀) (partialApp U ℕₚ P γ₁) (λ n m e → P .m-rel (Σᵤ-pair Γ ℕₚ γ₀ n) (Σᵤ-pair Γ ℕₚ γ₁ m) (mkΣ γe e))
    (tmApp (P [ sg ℕₚ zeroₚ ]ᵀ) Pz γ₀) (tmApp (P [ sg ℕₚ zeroₚ ]ᵀ) Pz γ₁) (tmAppEq (P [ sg ℕₚ zeroₚ ]ᵀ) Pz γe)
    (tmApp (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))) Ps γ₀) (tmApp (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))) Ps γ₁)
    (tmAppEq (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))) Ps γe) (tmApp ℕₚ n γ₀) (tmApp ℕₚ n γ₁) (tmAppEq ℕₚ n γe)
ℕrec {Γ} P Pz Ps n .t-refl γ =
  ℕrec-refl (partialApp U ℕₚ P γ) (tmApp (P [ sg ℕₚ zeroₚ ]ᵀ) Pz γ) (tmApp (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))) Ps γ) (tmApp ℕₚ n γ) 

ℕrec[] : {Γ Δ : Con} (σ : Sub Δ Γ) (P : Ty (Γ ▹ ℕₚ)) 
         (Pz : Tm Γ (P [ sg ℕₚ zeroₚ ]ᵀ)) (Ps : Tm Γ (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))))
         (n : Tm Γ ℕₚ) → ((ℕrec {Γ} P Pz Ps n) [ σ ]ᵗ) .t-el ≡ (ℕrec {Δ} (P [ ↑ σ ℕₚ ]ᵀ) (Pz [ σ ]ᵗ) (Ps [ σ ]ᵗ) (n [ σ ]ᵗ)) .t-el
ℕrec[] σ P Pz Ps n = refl -- holds definitionally

ℕrec-zero : {Γ : Con} (P : Ty (Γ ▹ ℕₚ)) (Pz : Tm Γ (P [ sg ℕₚ zeroₚ ]ᵀ)) (Ps : Tm Γ (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ))))
          → ℕrec P Pz Ps zeroₚ ≡ Pz
ℕrec-zero P Pz Ps = refl -- holds definitionally

ℕrec-suc : {Γ : Con} (P : Ty (Γ ▹ ℕₚ)) (Pz : Tm Γ (P [ sg ℕₚ zeroₚ ]ᵀ)) (Ps : Tm Γ (Πₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ)))) (n : Tm Γ ℕₚ)
         → ℕrec P Pz Ps (sucₚ n) ≡ appₚ (P [ sg ℕₚ n ]ᵀ) (P [ sg ℕₚ (sucₚ n) ∘ (wk (P [ sg ℕₚ n ]ᵀ)) ]ᵀ) (appₚ ℕₚ (Πₚ P (P [ sucSub Γ ∘ wk P ]ᵀ)) Ps n) (ℕrec P Pz Ps n)
ℕrec-suc P Pz Ps n = refl -- holds definitionally
