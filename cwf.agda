{-# OPTIONS --prop --rewriting --lossy-unification #-}

open import Agda.Primitive
open import lib
open import setoids
open import typeformers
open import views
open import fibrancy

-- CATEGORY WITH FAMILIES

-- Category of contexts and substitutions

Con : Set₁
Con = SetoidPt U

Sub : Con → Con → Set
Sub Γ Δ = SetoidMorphism (El Γ) (El Δ)

id : (Γ : Con) → Sub Γ Γ
id Γ .m-el γ = γ .p-el
id Γ .m-rel γ₁ γ₂ γe = γe
id Γ .m-refl γ = γ .p-refl

-- _∘_ : {Γ Δ Θ : Con} (σ : Sub Δ Γ) (τ : Sub Θ Δ) → Sub Θ Γ

id-left : {Γ Δ : Con} (σ : Sub Δ Γ) → id Γ ∘ σ ≡ σ
id-left σ = refl

id-right : {Γ Δ : Con} (σ : Sub Δ Γ) → σ ∘ id Δ ≡ σ
id-right σ = refl

assoc : {Γ Δ Θ Ξ : Con} (σ : Sub Δ Γ) (τ : Sub Θ Δ) (θ : Sub Ξ Θ) → σ ∘ (τ ∘ θ) ≡ (σ ∘ τ) ∘ θ
assoc σ τ θ = refl

-- Terminal object

◇ : Con
◇ = Embᵤ Unit (mkLift₁ (mkΣ (λ _ → ★) λ _ → ★))

ε : (Γ : Con) → Sub Γ ◇
ε Γ .m-el γ = ★
ε Γ .m-rel γ₁ γ₂ γe = ★
ε Γ .m-refl γ = tt

◇-η : {Γ : Con} (σ : Sub Γ ◇) → σ ≡ ε Γ
◇-η σ = refl

-- Presheaf of types

Ty : (Γ : Con) → Set₁
Ty Γ = SetoidMorphism (El Γ) U

_[_]ᵀ : {Γ Δ : Con} (A : Ty Γ) (σ : Sub Δ Γ) → Ty Δ
_[_]ᵀ A σ = A ∘ σ

[id]ᵀ : {Γ : Con} (A : Ty Γ) → A [ id Γ ]ᵀ ≡ A
[id]ᵀ A = refl

[∘]ᵀ : {Γ Δ Θ : Con} (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) → A [ σ ∘ τ ]ᵀ ≡ A [ σ ]ᵀ [ τ ]ᵀ
[∘]ᵀ A σ τ = refl

-- Dependent presheaf of small terms

record Tm (Γ : Con) (A : Ty Γ) : Set₁ where
  constructor mkTm
  field
    t-el : (γ : SetoidPt (El Γ)) → El (setoidApp A γ) .s-el
    t-rel : (γ₀ γ₁ : SetoidPt (El Γ)) (e : SetoidEq γ₀ γ₁) → El-eq (setoidApp A γ₀ .p-el .U-inU) (setoidApp A γ₁ .p-el .U-inU) (t-el γ₀) (t-el γ₁)
    t-refl : (γ : SetoidPt (El Γ)) → El-refl (setoidApp A γ .p-el .U-inU₂) (t-el γ) (t-rel γ γ (γ .p-rel))

open Tm public

_[_]ᵗ : {Γ Δ : Con} {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) → Tm Δ (A [ σ ]ᵀ)
_[_]ᵗ a σ .t-el δ = a .t-el (setoidApp σ δ)
_[_]ᵗ a σ .t-rel δ δ₂ δe = a .t-rel (setoidApp σ δ) (setoidApp σ δ₂) (σ .m-rel δ δ₂ δe)
_[_]ᵗ a σ .t-refl δ = a .t-refl (setoidApp σ δ)

[id]ᵗ : {Γ : Con} {A : Ty Γ} (a : Tm Γ A) → a [ id Γ ]ᵗ ≡ a
[id]ᵗ a = refl

[∘]ᵗ : {Γ Δ Θ : Con} {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) → a [ σ ∘ τ ]ᵗ ≡ a [ σ ]ᵗ [ τ ]ᵗ
[∘]ᵗ a σ τ = refl

-- Context extension

_▹_ : (Γ : Con) (A : Ty Γ) → Con
_▹_ Γ A = Σᵤ Γ A

wk : {Γ : Con} (A : Ty Γ) → Sub (Γ ▹ A) Γ
wk {Γ} A .m-el x = Σᵤ-fst-el Γ A x
wk {Γ} A .m-rel x y e = Σᵤ-fst-rel Γ Γ (Γ .p-rel) A A (A .m-rel) x y e
wk {Γ} A .m-refl x = Σᵤ-fst-refl Γ A x

var0 : {Γ : Con} (A : Ty Γ) → Tm (Γ ▹ A) (A [ wk A ]ᵀ)
var0 {Γ} A .t-el x = Σᵤ-snd-el Γ A x
var0 {Γ} A .t-rel x y e = Σᵤ-snd-rel Γ Γ (Γ .p-rel) A A (A .m-rel) x y e
var0 {Γ} A .t-refl x = Σᵤ-snd-refl Γ A x

pair : {Γ Δ : Con} (σ : Sub Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ σ ]ᵀ)) → Sub Δ (Γ ▹ A)
pair σ a .m-el δ = mkΣ (setoidApp σ δ) (a .t-el δ)
pair σ a .m-rel δ δ₂ δe = mkΣ (σ .m-rel δ δ₂ δe) (a .t-rel δ δ₂ δe)
pair σ a .m-refl δ = mk& refl (a .t-refl δ)

▹β₁ : {Γ Δ : Con} (σ : Sub Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ σ ]ᵀ)) → wk A ∘ pair σ a ≡ σ
▹β₁ σ a = refl

▹β₂ : {Γ Δ : Con} (σ : Sub Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ σ ]ᵀ)) → (var0 A) [ pair σ a ]ᵗ  ≡ a
▹β₂ σ a = refl

-- Helpers

sg : {Γ : Con} (A : Ty Γ) (a : Tm Γ A) → Sub Γ (Γ ▹ A)
sg A a = pair (id _) {A = A} a

↑ : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) → Sub (Δ ▹ (A [ σ ]ᵀ)) (Γ ▹ A)
↑ σ A = pair (σ ∘ (wk (A [ σ ]ᵀ))) (var0 (A [ σ ]ᵀ))

partialApp : {ℓ : Level} {A : SetoidPt U} (B : Setoid ℓ) (P : SetoidMorphism (El A) U) (Q : SetoidMorphism (El (Σᵤ A P)) B)
             (a : SetoidPt (El A)) → SetoidMorphism (El (setoidApp P a)) B
partialApp {A = A} B P Q a = mkMorphism (λ p → m-el Q (Σᵤ-pair A P a p))
                                        (λ p₀ p₁ pe → m-rel Q (Σᵤ-pair A P a p₀) (Σᵤ-pair A P a p₁) (mkΣ (a .p-rel) pe))
                                        (λ p → m-refl Q (Σᵤ-pair A P a p))

tmApp : {Γ : Con} (A : Ty Γ) (t : Tm Γ A) (γ : SetoidPt (El Γ)) → SetoidPt (El (setoidApp A γ))
tmApp A t γ = mkPt (t .t-el γ) (t .t-rel γ γ (γ .p-rel)) (t .t-refl γ)

-- Dependent products

Πₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty Γ
Πₚ A B = mkMorphism (λ γ → Πᵤ-el (setoidApp A γ) (partialApp U A B γ))
                    (λ γ₀ γ₁ γe → Πᵤ-rel (setoidApp A γ₀) (setoidApp A γ₁) (A .m-rel γ₀ γ₁ γe) (partialApp U A B γ₀) (partialApp U A B γ₁)
                                         (λ a₀ a₁ ae → m-rel B (Σᵤ-pair _ A γ₀ a₀) (Σᵤ-pair _ A γ₁ a₁) (mkΣ γe ae)))
                    (λ γ → Πᵤ-refl (setoidApp A γ) (partialApp U A B γ))

Π[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) → (Πₚ A B) [ σ ]ᵀ ≡ Πₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ)
Π[] σ A B = refl

λₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm (Γ ▹ A) B) → Tm Γ (Πₚ A B)
λₚ {Γ} A B t = mkTm (λ γ a → t .t-el (Σᵤ-pair Γ A γ a))
                    (λ γ₀ γ₁ γe a₀ a₁ ae → t .t-rel (Σᵤ-pair Γ A γ₀ a₀) (Σᵤ-pair Γ A γ₁ a₁) (mkΣ γe ae))
                    (λ γ a → t .t-refl (Σᵤ-pair Γ A γ a))

λ[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm (Γ ▹ A) B) → (λₚ A B t) [ σ ]ᵗ ≡ λₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ) (t [ ↑ σ A ]ᵗ)
λ[] σ A B t = refl

appₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ (Πₚ A B)) (u : Tm Γ A) → Tm Γ (B [ sg A u ]ᵀ)
appₚ A B t u = mkTm (λ γ → t .t-el γ (tmApp A u γ))
                    (λ γ₀ γ₁ γe → t .t-rel γ₀ γ₁ γe (tmApp A u γ₀) (tmApp A u γ₁) (u .t-rel γ₀ γ₁ γe))
                    (λ γ → t .t-refl γ (tmApp A u γ))

app[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ (Πₚ A B)) (u : Tm Γ A)
        → (appₚ A B t u) [ σ ]ᵗ ≡ appₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ) (t [ σ ]ᵗ) (u [ σ ]ᵗ)
app[] σ A B t u = refl

Πβ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm (Γ ▹ A) B) (u : Tm Γ A) → appₚ A B (λₚ A B t) u ≡ t [ sg A u ]ᵗ
Πβ A B t u = refl

-- Πη : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ (Πₚ A B)) → t ≡ λₚ A B {!appₚ (A [ wk A ]ᵀ) (B [ ↑ (wk A) A ]ᵀ) (t [ wk A ]ᵗ) (var0 A)!}
-- Πη = {!!}

-- Natural numbers

ℕₚ : {Γ : Con} → Ty Γ
ℕₚ {Γ} .m-el γ = mkU ℕ cℕ c₂ℕ c₃ℕ
ℕₚ {Γ} .m-rel γ₀ γ₁ γe = ★₁
ℕₚ {Γ} .m-refl γ = tt₁

ℕ[] : {Γ Δ : Con} (σ : Sub Δ Γ) → ℕₚ [ σ ]ᵀ ≡ ℕₚ
ℕ[] σ = refl

zeroₚ : {Γ : Con} → Tm Γ ℕₚ
zeroₚ {Γ} .t-el γ = zero
zeroₚ {Γ} .t-rel γ₀ γ₁ γe = nateq-zero
zeroₚ {Γ} .t-refl γ = tt

zero[] : {Γ Δ : Con} (σ : Sub Δ Γ) → zeroₚ [ σ ]ᵗ ≡ zeroₚ 
zero[] σ = refl

sucₚ : {Γ : Con} (n : Tm Γ ℕₚ) → Tm Γ ℕₚ
sucₚ n .t-el γ = suc (n .t-el γ)
sucₚ n .t-rel γ₀ γ₁ γe = nateq-suc (n .t-rel γ₀ γ₁ γe)
sucₚ n .t-refl γ = tt

suc[] : {Γ Δ : Con} (σ : Sub Δ Γ) (n : Tm Γ ℕₚ) → (sucₚ n) [ σ ]ᵗ ≡ sucₚ (n [ σ ]ᵗ)
suc[] σ n = refl
