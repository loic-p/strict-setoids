{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive

module lib where

infix 4 _≡_

record Σ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (P : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mkΣ
  field
    fst : A
    snd : P fst

open Σ public

record & {ℓ₁ ℓ₂ : Level} (A : Prop ℓ₁) (P : A → Prop ℓ₂) : Prop (ℓ₁ ⊔ ℓ₂) where
  constructor mk&
  field
    fst : A
    snd : P fst

open & public

record Unit : Set where
  constructor ★

open Unit public

record ⊤ : Prop where
  constructor tt

record Unit₁ : Set₁ where
  constructor ★₁

open Unit₁ public

record ⊤₁ : Prop₁ where
  constructor tt₁

data Empty : Set where

data ⊥ : Prop where

data Empty₁ : Set₁ where

data ⊥₁ : Prop₁ where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data _≡_ {ℓ : Level} {A : Set ℓ} (a : A) : A → Prop ℓ where
  refl : a ≡ a

record Lift₁ (A : Set) : Set₁ where
  constructor mkLift₁
  field
    lift₁ : A

open Lift₁ public

postulate transp : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {a : A} (P : A → Set ℓ₂) {b : A} (e : a ≡ b) (t : P a) → P b
postulate transpᵢ : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {a : A} (P : A → Prop ℓ₂) {b : A} (e : a ≡ b) (t : P a) → P b
postulate transp-refl : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {a : A} (P : A → Set ℓ₂) (e : a ≡ a) (t : P a) → transp P e t ≡ t

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE transp-refl   #-}

sym : {ℓ : Level} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

J : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {a : A} (P : (b : A) → a ≡ b → Set ℓ₂) {b : A} (e : a ≡ b) (t : P a refl) → P b e
J {a = a} P {b = b} e t = transp (λ b → (e : a ≡ b) → P b e) e (λ e → t) e

J₂ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {a : A} {B : Set ℓ₂} {b : B} (P : (a' : A) → a ≡ a' → (b' : B) → b ≡ b' → Set ℓ₃) {a' : A} (e : a ≡ a') {b' : B} (f : b ≡ b')
     → (t : P a refl b refl) → P a' e b' f
J₂ {a = a} {B = B} {b = b} P e = J (λ a' e → {b' : B} (f : b ≡ b') (t : P a refl b refl) → P a' e b' f) e (J (P a refl))

data nateq : ℕ → ℕ → Set where
  nateq-zero : nateq zero zero
  nateq-suc : {n m : ℕ} → nateq n m → nateq (suc n) (suc m)

_↔_ : {ℓ₁ ℓ₂ : Level} (P : Set ℓ₁) (Q : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
P ↔ Q = Σ (P → Q) (λ _ → Q → P)

equiv-refl : {ℓ : Level} (P : Set ℓ) → P ↔ P
equiv-refl P = mkΣ (λ x → x) (λ x → x)
