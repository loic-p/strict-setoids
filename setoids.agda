{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import lib

module setoids where

record Setoid (ℓ : Level) : Set (lsuc ℓ) where
  constructor mkSetoid
  field
    s-el : Set ℓ
    s-rel : s-el → s-el → Set ℓ
    s-refl : (x : s-el) → s-rel x x → Prop ℓ

open Setoid

record SetoidPt {ℓ : Level} (X : Setoid ℓ) : Set ℓ where
  constructor mkPt
  field
    p-el : s-el X
    p-rel : s-rel X p-el p-el
    p-refl : s-refl X p-el p-rel

open SetoidPt

SetoidPt-eq₂ : {ℓ : Level} (X : Setoid ℓ) {x₀ : s-el X} {x₁ x₁' : s-rel X x₀ x₀} (e : x₁ ≡ x₁') (x₂ : s-refl X x₀ x₁) (x₂' : s-refl X x₀ x₁')
             → mkPt {X = X} x₀ x₁ x₂ ≡ mkPt {X = X} x₀ x₁' x₂'
SetoidPt-eq₂ X refl x₂ x₂' = refl

SetoidEq : {ℓ : Level} {X : Setoid ℓ} (x y : SetoidPt X) → Set ℓ
SetoidEq {X = X} x y = s-rel X (p-el x) (p-el y)

record SetoidMorphism {ℓ₁ ℓ₂ : Level} (X : Setoid ℓ₁) (Y : Setoid ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    m-el : (x : SetoidPt X) → s-el Y
    m-rel : (x y : SetoidPt X) (e : SetoidEq x y) → s-rel Y (m-el x) (m-el y)
    m-refl : (x : SetoidPt X) → s-refl Y (m-el x) (m-rel x x (p-rel x))

open SetoidMorphism

setoidApp : {ℓ₁ ℓ₂ : Level} {X : Setoid ℓ₁} {Y : Setoid ℓ₂} (f : SetoidMorphism X Y) (x : SetoidPt X) → SetoidPt Y
setoidApp f x .p-el = m-el f x
setoidApp f x .p-rel = m-rel f x x (p-rel x)
setoidApp f x .p-refl = m-refl f x

setoidAppEq : {ℓ₁ ℓ₂ : Level} {X : Setoid ℓ₁} {Y : Setoid ℓ₂} (f : SetoidMorphism X Y) (x y : SetoidPt X) (e : SetoidEq x y) → SetoidEq (setoidApp f x) (setoidApp f y)
setoidAppEq f x y e = m-rel f x y e

record DepSetoid {ℓ₁ : Level} (A : Setoid ℓ₁) (ℓ₂ : Level) : Set (ℓ₁ ⊔ lsuc ℓ₂) where
  constructor MkDepSetoid
  field
    d-el : (a : SetoidPt A) → Set ℓ₂
    d-rel : (a : SetoidPt A) (p : d-el a) (b : SetoidPt A) (q : d-el b) → Set ℓ₂
    d-refl : (a : SetoidPt A) (p : d-el a) (e : d-rel a p a p) → Prop ℓ₂

open DepSetoid

fiber : {ℓ₁ ℓ₂ : Level} (A : Setoid ℓ₁) (P : DepSetoid A ℓ₂) (a : SetoidPt A) → Setoid ℓ₂
fiber A P a .s-el = d-el P a
fiber A P a .s-rel p q = d-rel P a p a q
fiber A P a .s-refl p e = d-refl P a p e

record SetoidSection {ℓ₁ ℓ₂ : Level} (A : Setoid ℓ₁) (P : DepSetoid A ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    r-el : (a : SetoidPt A) → d-el P a
    r-rel : (a b : SetoidPt A) (e : SetoidEq a b) → d-rel P a (r-el a) b (r-el b)
    r-refl : (a : SetoidPt A) → d-refl P a (r-el a) (r-rel a a (p-rel a))

open SetoidSection

SetoidΠ : {ℓ₁ ℓ₂ : Level} (A : Setoid ℓ₁) (P : DepSetoid A ℓ₂) → Setoid (ℓ₁ ⊔ ℓ₂)
SetoidΠ A P .s-el = (a : SetoidPt A) → d-el P a 
SetoidΠ A P .s-rel f g = (a b : SetoidPt A) (e : SetoidEq a b) → d-rel P a (f a) b (g b)
SetoidΠ A P .s-refl f e = (a : SetoidPt A) → d-refl P a (f a) (e a a (p-rel a))

SetoidΣ : {ℓ₁ ℓ₂ : Level} (A : Setoid ℓ₁) (P : DepSetoid A ℓ₂) → Setoid (ℓ₁ ⊔ ℓ₂)
SetoidΣ A P .s-el = Σ (SetoidPt A) (λ a → d-el P a)
SetoidΣ A P .s-rel x y = Σ (SetoidEq (x .fst) (y .fst)) (λ _ → d-rel P (x .fst) (x .snd) (y .fst) (y .snd))
SetoidΣ A P .s-refl x e = & (x .fst .p-rel ≡ e .fst) (λ _ → d-refl P (x .fst) (x .snd) (e .snd))

Setoidℕ : Setoid lzero
Setoidℕ .s-el = ℕ
Setoidℕ .s-rel x y = nateq x y
Setoidℕ .s-refl x e = ⊤

data inU : Set → Set₁ where
  cΠ : (A : Setoid lzero) (Au : inU (A .s-el)) (P : DepSetoid A lzero) (Pu : (a : SetoidPt A) → inU (P .d-el a)) → inU ((a : SetoidPt A) → P .d-el a) 
  cΣ : (A : Setoid lzero) (Au : inU (A .s-el)) (P : DepSetoid A lzero) (Pu : (a : SetoidPt A) → inU (P .d-el a)) → inU (Σ (SetoidPt A) (P .d-el))
  cℕ : inU ℕ
  cEmb : (P : Set) → inU P

El-eq : {A : Set} (Au : inU A) {B : Set} (Bu : inU B) (a : A) (b : B) → Set
El-eq (cΠ A Au P Pu) (cΠ B Bu Q Qu) f g = (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → El-eq (Pu a) (Qu b) (f a) (g b)
El-eq (cΠ A Au P Pu) (cΣ B Bu Q Qu) a b = Empty
El-eq (cΠ A Au P Pu) cℕ a b = Empty
El-eq (cΠ A Au P Pu) (cEmb Q) a b = Empty
El-eq (cΣ A Au P Pu) (cΠ B Bu Q Qu) a b = Empty
El-eq (cΣ A Au P Pu) (cΣ B Bu Q Qu) a b = Σ (El-eq Au Bu (a .fst .p-el) (b .fst .p-el)) (λ _ → El-eq (Pu (a .fst)) (Qu (b .fst)) (a .snd) (b .snd))
El-eq (cΣ A Au P Pu) cℕ a b = Empty
El-eq (cΣ A Au P Pu) (cEmb P₁) a b = Empty
El-eq cℕ (cΠ A Bu P Pu) a b = Empty
El-eq cℕ (cΣ A Bu P Pu) a b = Empty
El-eq cℕ cℕ n m = nateq n m
El-eq cℕ (cEmb P) a b = Empty
El-eq (cEmb P) (cΠ B Bu Q Qu) a b = Empty
El-eq (cEmb P) (cΣ B Bu Q Qu) a b = Empty
El-eq (cEmb P) cℕ a b = Empty
El-eq (cEmb P) (cEmb Q) a b = Unit

U-eq : {A : Set} (Au : inU A) {B : Set} (Bu : inU B) → Set
U-eq (cΠ A Au P Pu) (cΠ B Bu Q Qu) = (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → U-eq (Pu a) (Qu b)
U-eq (cΠ A Au P Pu) (cΣ B Bu Q Qu) = Empty
U-eq (cΠ A Au P Pu) cℕ = Empty
U-eq (cΠ A Au P Pu) (cEmb Q) = Empty
U-eq (cΣ A Au P Pu) (cΠ B Bu Q Qu) = Empty
U-eq (cΣ A Au P Pu) (cΣ B Bu Q Qu) = (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → U-eq (Pu a) (Qu b)
U-eq (cΣ A Au P Pu) cℕ = Empty
U-eq (cΣ A Au P Pu) (cEmb Q) = Empty
U-eq cℕ (cΠ A Bu P Pu) = Empty
U-eq cℕ (cΣ A Bu P Pu) = Empty
U-eq cℕ cℕ = Unit
U-eq cℕ (cEmb P) = Empty
U-eq (cEmb P) (cΠ B Bu Q Qu) = Empty
U-eq (cEmb P) (cΣ B Bu Q Qu) = Empty
U-eq (cEmb P) cℕ = Empty
U-eq (cEmb P) (cEmb Q) = P ↔ Q

data inU₂ : (A : Set) (Au : inU A) → Set₁ where
  c₂Π : (A : Set) (Au : inU A) (Ar : (a : A) → El-eq Au Au a a → Prop) (Av : inU₂ A Au)
        (P : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → Set) (Pu : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → inU (P a))
        (Pr : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) (p : P a) (pe : El-eq (Pu a) (Pu a) p p) → Prop)
        (Pv : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → inU₂ (P a) (Pu a))
        → inU₂ ((a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → P a) (cΠ (mkSetoid A (El-eq Au Au) Ar) Au (MkDepSetoid P (λ a p b q → El-eq (Pu a) (Pu b) p q) Pr) Pu)
  c₂Σ : (A : Set) (Au : inU A) (Ar : (a : A) → El-eq Au Au a a → Prop) (Av : inU₂ A Au)
        (P : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → Set) (Pu : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → inU (P a))
        (Pr : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) (p : P a) (pe : El-eq (Pu a) (Pu a) p p) → Prop)
        (Pv : (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → inU₂ (P a) (Pu a))
        → inU₂ (Σ (SetoidPt (mkSetoid A (El-eq Au Au) Ar)) P) (cΣ (mkSetoid A (El-eq Au Au) Ar) Au (MkDepSetoid P (λ a p b q → El-eq (Pu a) (Pu b) p q) Pr) Pu)
  c₂ℕ : inU₂ ℕ cℕ
  c₂Emb : (P : Set) → inU₂ P (cEmb P)

El-refl : {A : Set} {Au : inU A} (Av : inU₂ A Au) (a : A) (ae : El-eq Au Au a a) → Prop
El-refl (c₂Π A Au Ar Av P Pu Pr Pv) f fe = (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → El-refl (Pv a) (f a) (fe a a (a .p-rel))
El-refl (c₂Σ A Au Ar Av P Pu Pr Pv) a ae = & (a .fst .p-rel ≡ ae .fst) (λ _ → El-refl (Pv (a .fst)) (a .snd) (ae .snd)) 
El-refl c₂ℕ a ae = ⊤
El-refl (c₂Emb P) a ae = ⊤

U-refl : {A : Set} {Au : inU A} (Av : inU₂ A Au) → U-eq Au Au → Prop
U-refl (c₂Π A Au Ar Av P Pu Pr Pv) e = (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → U-refl (Pv a) (e a a (a .p-rel))
U-refl (c₂Σ A Au Ar Av P Pu Pr Pv) e = (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → U-refl (Pv a) (e a a (a .p-rel))
U-refl c₂ℕ e = ⊤
U-refl (c₂Emb P) e = e ≡ equiv-refl P

data inU₃ : (A : Set) (Au : inU A) (Av : inU₂ A Au) → Set₁ where
  c₃Π : (A : Set) (Au : inU A) (Av : inU₂ A Au) (Aw : inU₃ A Au Av)
        (P : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → Set) (Pu : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU (P a))
        (Pv : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₂ (P a) (Pu a))
        (Pw : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₃ (P a) (Pu a) (Pv a))
        (P-rel : (a b : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) (e : El-eq Au Au (a .p-el) (b .p-el)) → U-eq (Pu a) (Pu a))
        (P-refl : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → U-refl (Pv a) (P-rel a a (a .p-rel)))
        → inU₃ ((a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → P a)
               (cΠ (mkSetoid A (El-eq Au Au) (El-refl Av)) Au (MkDepSetoid P (λ a p b q → El-eq (Pu a) (Pu b) p q) (λ a p e → El-refl (Pv a) p e)) Pu)
               (c₂Π A Au (El-refl Av) Av P Pu (λ a → El-refl (Pv a)) Pv)
  c₃Σ : (A : Set) (Au : inU A) (Av : inU₂ A Au) (Aw : inU₃ A Au Av)
        (P : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → Set) (Pu : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU (P a))
        (Pv : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₂ (P a) (Pu a))
        (Pw : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₃ (P a) (Pu a) (Pv a))
        (P-rel : (a b : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) (e : El-eq Au Au (a .p-el) (b .p-el)) → U-eq (Pu a) (Pu a))
        (P-refl : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → U-refl (Pv a) (P-rel a a (a .p-rel)))
        → inU₃ (Σ (SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) P)
               (cΣ (mkSetoid A (El-eq Au Au) (El-refl Av)) Au (MkDepSetoid P (λ a p b q → El-eq (Pu a) (Pu b) p q) (λ a p e → El-refl (Pv a) p e)) Pu)
               (c₂Σ A Au (El-refl Av) Av P Pu (λ a → El-refl (Pv a)) Pv)
  c₃ℕ : inU₃ ℕ cℕ c₂ℕ
  c₃Emb : (P : Set) → inU₃ P (cEmb P) (c₂Emb P)


