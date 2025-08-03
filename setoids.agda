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
    f-el : (a : SetoidPt A) → d-el P a
    f-rel : (a b : SetoidPt A) (e : SetoidEq a b) → d-rel P a (f-el a) b (f-el b)
    f-refl : (a : SetoidPt A) → d-refl P a (f-el a) (f-rel a a (p-rel a))

open SetoidSection public

record SetoidRelation {ℓ : Level} (A : Setoid ℓ) : Set (lsuc ℓ) where
  constructor mkRelation
  field
    r-el : (a b : SetoidPt A) → Set ℓ
    r-rel : (a₀ a₁ : SetoidPt A) (ae : SetoidEq a₀ a₁) (b₀ b₁ : SetoidPt A) (be : SetoidEq b₀ b₁) → r-el a₀ b₀ ↔ r-el a₁ b₁
    r-refl : ⊤

open SetoidRelation public

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

data closure {ℓ : Level} (A : Setoid ℓ) (R : (a b : SetoidPt A) → Set ℓ) (a : SetoidPt A) : SetoidPt A → Set ℓ where
  clo-refl : closure A R a a
  clo-cons : (b c : SetoidPt A) → R b c → closure A R a b → closure A R a c
  clo-anticons : (b c : SetoidPt A) → R c b → closure A R a b → closure A R a c

record quoEq {ℓ : Level} (A B : Setoid ℓ) (eAB : SetoidPt A → SetoidPt B → Set ℓ) (R : SetoidPt A → SetoidPt A → Set ℓ) (S : SetoidPt B → SetoidPt B → Set ℓ)
              (a : SetoidPt A) (b : SetoidPt B) : Set ℓ where
  constructor mkQuoEq
  field
    qe-a' : SetoidPt A
    qe-b' : SetoidPt B
    qe-a'≡b' : eAB qe-a' qe-b'
    qe-a≡a' : closure A R a qe-a'
    qe-b≡b' : closure B S b qe-b'
    
open quoEq public

data quoEq-refl {ℓ : Level} (A : Setoid ℓ) (rA : (a : SetoidPt A) → A .s-rel (a .p-el) (a .p-el) → Prop ℓ)
                (R : (a b : SetoidPt A) → Set ℓ) (a : SetoidPt A) : quoEq A A (λ a b → A .s-rel (a .p-el) (b .p-el)) R R a a → Prop ℓ where
  mkQuoEqRefl : (r : rA a (a .p-rel)) → quoEq-refl A rA R a (mkQuoEq a a (a .p-rel) clo-refl clo-refl)

data inU : Set → Set₁ where
  cΠ : (A : Setoid lzero) (Au : inU (A .s-el)) (P : DepSetoid A lzero) (Pu : (a : SetoidPt A) → inU (P .d-el a)) → inU ((a : SetoidPt A) → P .d-el a) 
  cΣ : (A : Setoid lzero) (Au : inU (A .s-el)) (P : DepSetoid A lzero) (Pu : (a : SetoidPt A) → inU (P .d-el a)) → inU (Σ (SetoidPt A) (P .d-el))
  cℕ : inU ℕ
  cℚ : (A : Setoid lzero) (Au : inU (A .s-el)) (R : (a b : SetoidPt A) → Set) → inU (SetoidPt A)
  cEmb : (P : Set) → inU P

El-eq : {A : Set} (Au : inU A) {B : Set} (Bu : inU B) (a : A) (b : B) → Set
El-eq (cΠ A Au P Pu) (cΠ B Bu Q Qu) f g = (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → El-eq (Pu a) (Qu b) (f a) (g b)
El-eq (cΣ A Au P Pu) (cΣ B Bu Q Qu) a b = Σ (El-eq Au Bu (a .fst .p-el) (b .fst .p-el)) (λ _ → El-eq (Pu (a .fst)) (Qu (b .fst)) (a .snd) (b .snd))
El-eq cℕ cℕ n m = nateq n m
El-eq (cℚ A Au R) (cℚ B Bu S) a b = quoEq A B (λ a b → El-eq Au Bu (a .p-el) (b .p-el)) R S a b 
El-eq (cEmb P) (cEmb Q) a b = Unit
El-eq _ _ a b = Empty

U-eq : {A : Set} (Au : inU A) {B : Set} (Bu : inU B) → Set₁
U-eq (cΠ A Au P Pu) (cΠ B Bu Q Qu) = Σ (U-eq Au Bu) (λ _ → (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → U-eq (Pu a) (Qu b))
U-eq (cΣ A Au P Pu) (cΣ B Bu Q Qu) = Σ (U-eq Au Bu) (λ _ → (a : SetoidPt A) (b : SetoidPt B) → El-eq Au Bu (a .p-el) (b .p-el) → U-eq (Pu a) (Qu b))
U-eq cℕ cℕ = Unit₁
U-eq (cℚ A Au R) (cℚ B Bu S) = Σ (U-eq Au Bu) (λ _ → (a₀ : SetoidPt A) (b₀ : SetoidPt B) (e₀ : El-eq Au Bu (a₀ .p-el) (b₀ .p-el))
                                                     (a₁ : SetoidPt A) (b₁ : SetoidPt B) (e₁ : El-eq Au Bu (a₁ .p-el) (b₁ .p-el)) → R a₀ a₁ ↔ S b₀ b₁)
U-eq (cEmb P) (cEmb Q) = Lift₁ (P ↔ Q)
U-eq _ _ = Empty₁

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
  c₂ℚ : (A : Set) (Au : inU A) (Ar : (a : A) → El-eq Au Au a a → Prop) (Av : inU₂ A Au)
        (R : (a b : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → Set)
        → inU₂ (SetoidPt (mkSetoid A (El-eq Au Au) Ar)) (cℚ (mkSetoid A (El-eq Au Au) Ar) Au R)
  c₂Emb : (P : Set) → inU₂ P (cEmb P)

El-refl : {A : Set} {Au : inU A} (Av : inU₂ A Au) (a : A) (ae : El-eq Au Au a a) → Prop
El-refl (c₂Π A Au Ar Av P Pu Pr Pv) f fe = (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → El-refl (Pv a) (f a) (fe a a (a .p-rel))
El-refl (c₂Σ A Au Ar Av P Pu Pr Pv) a ae = & (a .fst .p-rel ≡ ae .fst) (λ _ → El-refl (Pv (a .fst)) (a .snd) (ae .snd)) 
El-refl c₂ℕ a ae = ⊤
El-refl (c₂ℚ A Au Ar Av R) a ae = quoEq-refl (mkSetoid A (El-eq Au Au) Ar) (λ a ae → El-refl Av (a .p-el) ae) R a ae
El-refl (c₂Emb P) a ae = ⊤

U-refl : {A : Set} {Au : inU A} (Av : inU₂ A Au) → U-eq Au Au → Prop₁
U-refl (c₂Π A Au Ar Av P Pu Pr Pv) e = & (U-refl Av (e .fst)) (λ _ → (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → U-refl (Pv a) (e .snd a a (a .p-rel)))
U-refl (c₂Σ A Au Ar Av P Pu Pr Pv) e = & (U-refl Av (e .fst)) (λ _ → (a : SetoidPt (mkSetoid A (El-eq Au Au) Ar)) → U-refl (Pv a) (e .snd a a (a .p-rel)))
U-refl c₂ℕ e = ⊤₁
U-refl (c₂ℚ A Au Ar Av R) e = U-refl Av (e .fst)
U-refl (c₂Emb P) e = ⊤₁ -- e ≡ mkLift₁ (equiv-refl P)

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
  c₃ℚ : (A : Set) (Au : inU A) (Av : inU₂ A Au) (Aw : inU₃ A Au Av) (R : (a b : SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) → Set)
        → inU₃ (SetoidPt (mkSetoid A (El-eq Au Au) (El-refl Av))) (cℚ (mkSetoid A (El-eq Au Au) (El-refl Av)) Au R) (c₂ℚ A Au (λ a e → El-refl Av a e) Av R)
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

obseq-El : (A : SetoidPt U) (B : SetoidPt U) (a : SetoidPt (El A)) (b : SetoidPt (El B)) → Set
obseq-El A B a b = El-eq (A .p-el .U-inU) (B .p-el .U-inU) (a .p-el) (b .p-el)
