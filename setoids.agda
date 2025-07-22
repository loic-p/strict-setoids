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

open Setoid public

record SetoidPt {ℓ : Level} (X : Setoid ℓ) : Set ℓ where
  constructor mkPt
  field
    p-el : s-el X
    p-rel : s-rel X p-el p-el
    p-refl : s-refl X p-el p-rel

open SetoidPt public

SetoidPt-eq₂ : {ℓ : Level} (X : Setoid ℓ) {x₀ : s-el X} {x₁ x₁' : s-rel X x₀ x₀} (e : x₁ ≡ x₁') (x₂ : s-refl X x₀ x₁) (x₂' : s-refl X x₀ x₁')
             → mkPt {X = X} x₀ x₁ x₂ ≡ mkPt {X = X} x₀ x₁' x₂'
SetoidPt-eq₂ X refl x₂ x₂' = refl

SetoidEq : {ℓ : Level} {X : Setoid ℓ} (x y : SetoidPt X) → Set ℓ
SetoidEq {X = X} x y = s-rel X (p-el x) (p-el y)

record SetoidMorphism {ℓ₁ ℓ₂ : Level} (X : Setoid ℓ₁) (Y : Setoid ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mkMorphism
  field
    m-el : (x : SetoidPt X) → s-el Y
    m-rel : (x y : SetoidPt X) (e : SetoidEq x y) → s-rel Y (m-el x) (m-el y)
    m-refl : (x : SetoidPt X) → s-refl Y (m-el x) (m-rel x x (p-rel x))

open SetoidMorphism public

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

open DepSetoid public

fiber : {ℓ₁ ℓ₂ : Level} (A : Setoid ℓ₁) (P : DepSetoid A ℓ₂) (a : SetoidPt A) → Setoid ℓ₂
fiber A P a .s-el = d-el P a
fiber A P a .s-rel p q = d-rel P a p a q
fiber A P a .s-refl p e = d-refl P a p e

record SetoidSection {ℓ₁ ℓ₂ : Level} (A : Setoid ℓ₁) (P : DepSetoid A ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    r-el : (a : SetoidPt A) → d-el P a
    r-rel : (a b : SetoidPt A) (e : SetoidEq a b) → d-rel P a (r-el a) b (r-el b)
    r-refl : (a : SetoidPt A) → d-refl P a (r-el a) (r-rel a a (p-rel a))

open SetoidSection public

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

U-eq : {A : Set} (Au : inU A) {B : Set} (Bu : inU B) → Set₁
U-eq (cΠ A Au P Pu) (cΠ B Bu Q Qu) = Σ (U-eq Au Bu) (λ _ → (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → U-eq (Pu a) (Qu b))
U-eq (cΠ A Au P Pu) (cΣ B Bu Q Qu) = Empty₁
U-eq (cΠ A Au P Pu) cℕ = Empty₁
U-eq (cΠ A Au P Pu) (cEmb Q) = Empty₁
U-eq (cΣ A Au P Pu) (cΠ B Bu Q Qu) = Empty₁
U-eq (cΣ A Au P Pu) (cΣ B Bu Q Qu) = Σ (U-eq Au Bu) (λ _ → (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → U-eq (Pu a) (Qu b))
U-eq (cΣ A Au P Pu) cℕ = Empty₁
U-eq (cΣ A Au P Pu) (cEmb Q) = Empty₁
U-eq cℕ (cΠ A Bu P Pu) = Empty₁
U-eq cℕ (cΣ A Bu P Pu) = Empty₁
U-eq cℕ cℕ = Unit₁
U-eq cℕ (cEmb P) = Empty₁
U-eq (cEmb P) (cΠ B Bu Q Qu) = Empty₁
U-eq (cEmb P) (cΣ B Bu Q Qu) = Empty₁
U-eq (cEmb P) cℕ = Empty₁
U-eq (cEmb P) (cEmb Q) = Lift₁ (P ↔ Q)

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

U-refl : {A : Set} {Au : inU A} (Av : inU₂ A Au) → U-eq Au Au → Prop₁
U-refl (c₂Π A Au Ar Av P Pu Pr Pv) e = & (U-refl Av (e .fst)) (λ _ → (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → U-refl (Pv a) (e .snd a a (a .p-rel)))
U-refl (c₂Σ A Au Ar Av P Pu Pr Pv) e = & (U-refl Av (e .fst)) (λ _ → (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → U-refl (Pv a) (e .snd a a (a .p-rel)))
U-refl c₂ℕ e = ⊤₁
U-refl (c₂Emb P) e = e ≡ mkLift₁ (equiv-refl P)

data inU₃ : (A : Set) (Au : inU A) (Av : inU₂ A Au) → Set₁ where
  c₃Π : (A : Set) (Au : inU A) (Av : inU₂ A Au) (Aw : inU₃ A Au Av)
        (P : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → Set) (Pu : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU (P a))
        (Pv : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₂ (P a) (Pu a))
        (Pw : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₃ (P a) (Pu a) (Pv a))
        → inU₃ ((a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → P a)
               (cΠ (mkSetoid A (El-eq Au Au) (El-refl Av)) Au (MkDepSetoid P (λ a p b q → El-eq (Pu a) (Pu b) p q) (λ a p e → El-refl (Pv a) p e)) Pu)
               (c₂Π A Au (El-refl Av) Av P Pu (λ a → El-refl (Pv a)) Pv)
  c₃Σ : (A : Set) (Au : inU A) (Av : inU₂ A Au) (Aw : inU₃ A Au Av)
        (P : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → Set) (Pu : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU (P a))
        (Pv : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₂ (P a) (Pu a))
        (Pw : (a : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → inU₃ (P a) (Pu a) (Pv a))
        → inU₃ (Σ (SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) P)
               (cΣ (mkSetoid A (El-eq Au Au) (El-refl Av)) Au (MkDepSetoid P (λ a p b q → El-eq (Pu a) (Pu b) p q) (λ a p e → El-refl (Pv a) p e)) Pu)
               (c₂Σ A Au (El-refl Av) Av P Pu (λ a → El-refl (Pv a)) Pv)
  c₃ℕ : inU₃ ℕ cℕ c₂ℕ
  c₃Emb : (P : Set) → inU₃ P (cEmb P) (c₂Emb P)

record U-el : Set₁ where
  constructor mkU
  field
    U-set : Set
    U-inU : inU U-set
    U-inU₂ : inU₂ U-set U-inU
    U-inU₃ : inU₃ U-set U-inU U-inU₂

open U-el public

U : Setoid (lsuc lzero)
U .s-el = U-el
U .s-rel A B = U-eq (A .U-inU) (B .U-inU)
U .s-refl A Ae = U-refl (A .U-inU₂) Ae

U* : DepSetoid U lzero
U* .d-el A = A .p-el .U-set
U* .d-rel A a B b = El-eq (A .p-el .U-inU) (B .p-el .U-inU) a b
U* .d-refl A a ae = El-refl (A .p-el .U-inU₂) a ae

El : (A : SetoidPt U) → Setoid lzero
El A = fiber U U* A

ℕᵤ : SetoidPt U
ℕᵤ .p-el = mkU ℕ cℕ c₂ℕ c₃ℕ
ℕᵤ .p-rel = ★₁
ℕᵤ .p-refl = tt₁

Embᵤ : (P : Set) → SetoidPt U
Embᵤ P .p-el = mkU P (cEmb P) (c₂Emb P) (c₃Emb P)
Embᵤ P .p-rel = mkLift₁ (equiv-refl P)
Embᵤ P .p-refl = refl

Πᵤ-el : (A : SetoidPt U) (P : SetoidMorphism (El A) U) → U .s-el
Πᵤ-el A P = mkU _ _ _ (c₃Π (A .p-el .U-set) (A .p-el .U-inU) (A .p-el .U-inU₂) (A .p-el .U-inU₃) (λ a → P .m-el a .U-set)
                           (λ a → P .m-el a .U-inU) (λ a → P .m-el a .U-inU₂) (λ a → P .m-el a .U-inU₃)) 

Πᵤ-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (P₀ : SetoidMorphism (El A₀) U) (P₁ : SetoidMorphism (El A₁) U)
         (Pe : (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : U* .d-rel A₀ (a₀ .p-el) A₁ (a₁ .p-el)) → U .s-rel (P₀ .m-el a₀) (P₁ .m-el a₁))
         → U .s-rel (Πᵤ-el A₀ P₀) (Πᵤ-el A₁ P₁)
Πᵤ-rel A₀ A₁ Ae P₀ P₁ Pe = mkΣ Ae Pe

Πᵤ-refl : (A : SetoidPt U) (P : SetoidMorphism (El A) U) → U .s-refl (Πᵤ-el A P) (Πᵤ-rel A A (A .p-rel) P P (λ a₀ a₁ ae → P .m-rel a₀ a₁ ae))
Πᵤ-refl A P = mk& (A .p-refl) (λ a → P .m-refl a)

Πᵤ : (A : SetoidPt U) (P : SetoidMorphism (El A) U) → SetoidPt U
Πᵤ A P = mkPt (Πᵤ-el A P) (Πᵤ-rel A A (A .p-rel) P P (P .m-rel)) (Πᵤ-refl A P)

Σᵤ-el : (A : SetoidPt U) (P : SetoidMorphism (El A) U) → U .s-el
Σᵤ-el A P = mkU _ _ _ (c₃Σ (A .p-el .U-set) (A .p-el .U-inU) (A .p-el .U-inU₂) (A .p-el .U-inU₃) (λ a → P .m-el a .U-set)
                           (λ a → P .m-el a .U-inU) (λ a → P .m-el a .U-inU₂) (λ a → P .m-el a .U-inU₃)) 

Σᵤ-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (P₀ : SetoidMorphism (El A₀) U) (P₁ : SetoidMorphism (El A₁) U)
         (Pe : (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : U* .d-rel A₀ (a₀ .p-el) A₁ (a₁ .p-el)) → U .s-rel (P₀ .m-el a₀) (P₁ .m-el a₁))
         → U .s-rel (Σᵤ-el A₀ P₀) (Σᵤ-el A₁ P₁)
Σᵤ-rel A₀ A₁ Ae P₀ P₁ Pe = mkΣ Ae Pe

Σᵤ-refl : (A : SetoidPt U) (P : SetoidMorphism (El A) U) → U .s-refl (Σᵤ-el A P) (Σᵤ-rel A A (A .p-rel) P P (λ a₀ a₁ ae → P .m-rel a₀ a₁ ae))
Σᵤ-refl A P = mk& (A .p-refl) (λ a → P .m-refl a)

Σᵤ : (A : SetoidPt U) (P : SetoidMorphism (El A) U) → SetoidPt U
Σᵤ A P = mkPt (Σᵤ-el A P) (Σᵤ-rel A A (A .p-rel) P P (P .m-rel)) (Σᵤ-refl A P)
