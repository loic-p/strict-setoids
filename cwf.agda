{-# OPTIONS --prop --rewriting --lossy-unification #-}

open import Agda.Primitive
open import lib
open import setoids
open import typeformers
open import views
open import fibrancy

{- In this module, we define a Category with Families (CwF) of setoids from the universe U.
   Crucially, all the computation rules are definitional (in the code, they are proved by refl) -}

{- Category of contexts and substitutions -}

Con : Set₁
Con = SetoidPt U

Sub : Con → Con → Set
Sub Γ Δ = SetoidMorphism (El Γ) (El Δ)

id : (Γ : Con) → Sub Γ Γ
id Γ .m-el γ = γ .p-el
id Γ .m-rel γ₁ γ₂ γe = γe
id Γ .m-refl γ = γ .p-refl

id-left : {Γ Δ : Con} (σ : Sub Δ Γ) → id Γ ∘ σ ≡ σ
id-left σ = refl -- holds definitionally

id-right : {Γ Δ : Con} (σ : Sub Δ Γ) → σ ∘ id Δ ≡ σ
id-right σ = refl -- holds definitionally

assoc : {Γ Δ Θ Ξ : Con} (σ : Sub Δ Γ) (τ : Sub Θ Δ) (θ : Sub Ξ Θ) → σ ∘ (τ ∘ θ) ≡ (σ ∘ τ) ∘ θ
assoc σ τ θ = refl -- holds definitionally

{- Terminal object -}

◇ : Con
◇ = Embᵤ Unit (mkLift₁ (mkΣ (λ _ → ★) λ _ → ★))

ε : (Γ : Con) → Sub Γ ◇
ε Γ .m-el γ = ★
ε Γ .m-rel γ₁ γ₂ γe = ★
ε Γ .m-refl γ = tt

◇-η : {Γ : Con} (σ : Sub Γ ◇) → σ ≡ ε Γ
◇-η σ = refl -- holds definitionally

{- Presheaf of types -}

Ty : (Γ : Con) → Set₁
Ty Γ = SetoidMorphism (El Γ) U

_[_]ᵀ : {Γ Δ : Con} (A : Ty Γ) (σ : Sub Δ Γ) → Ty Δ
_[_]ᵀ A σ = A ∘ σ

[id]ᵀ : {Γ : Con} (A : Ty Γ) → A [ id Γ ]ᵀ ≡ A
[id]ᵀ A = refl -- holds definitionally

[∘]ᵀ : {Γ Δ Θ : Con} (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) → A [ σ ∘ τ ]ᵀ ≡ A [ σ ]ᵀ [ τ ]ᵀ
[∘]ᵀ A σ τ = refl -- holds definitionally

{- Dependent presheaf of small terms -}

record Tm (Γ : Con) (A : Ty Γ) : Set₁ where
  eta-equality
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
[id]ᵗ a = refl -- holds definitionally

[∘]ᵗ : {Γ Δ Θ : Con} {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) → a [ σ ∘ τ ]ᵗ ≡ a [ σ ]ᵗ [ τ ]ᵗ
[∘]ᵗ a σ τ = refl -- holds definitionally

{- Context extensions -}

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
▹β₁ σ a = refl -- holds definitionally

▹β₂ : {Γ Δ : Con} (σ : Sub Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ σ ]ᵀ)) → (var0 A) [ pair σ a ]ᵗ ≡ a
▹β₂ σ a = refl -- holds definitionally

{- Interestingly enough, η for morphisms into extended contexts does not hold for abstract
   elements of [Sub Δ (Γ ▹ A)]. This is because telescopes (iterated Σ) of setoids are highly
   redundant: equality proofs are duplicated all the time, along with irrelevant proofs that
   they are in fact equal to the original ones. -}

{- However, it does hold for elements of the form [pair σ a] -}

▹η-pair : {Γ Δ : Con} {A : Ty Γ} (σ : Sub Δ Γ) (a : Tm Δ (A [ σ ]ᵀ)) → (pair σ a) ≡ pair (wk A ∘ (pair σ a)) (var0 A [ pair σ a ]ᵗ)
▹η-pair σ a = refl -- holds definitionally

{- Thankfully, in the concrete syntax all substitutions are given by concrete lists of terms.
   Thus, even though we are seemingly missing some definitional equations in this file,
   this is still enough to get a syntactic translation of our observational type theory
   into MLTT. -}

{- Helpers for subtitutions -}

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

tmAppEq : {Γ : Con} (A : Ty Γ) (t : Tm Γ A) {γ₀ γ₁ : SetoidPt (El Γ)} (γe : SetoidEq γ₀ γ₁) → obseq-El (setoidApp A γ₀) (setoidApp A γ₁) (tmApp A t γ₀) (tmApp A t γ₁)
tmAppEq A t {γ₀} {γ₁} γe = t .t-rel γ₀ γ₁ γe

{- Now that the subsitution calculus works, we can look at type formers.
   Firstly, we have dependent products with β and η. -}

Πₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty Γ
Πₚ A B = mkMorphism (λ γ → Πᵤ-el (setoidApp A γ) (partialApp U A B γ))
                    (λ γ₀ γ₁ γe → Πᵤ-rel (setoidApp A γ₀) (setoidApp A γ₁) (A .m-rel γ₀ γ₁ γe) (partialApp U A B γ₀) (partialApp U A B γ₁)
                                         (λ a₀ a₁ ae → m-rel B (Σᵤ-pair _ A γ₀ a₀) (Σᵤ-pair _ A γ₁ a₁) (mkΣ γe ae)))
                    (λ γ → Πᵤ-refl (setoidApp A γ) (partialApp U A B γ))

Π[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) → (Πₚ A B) [ σ ]ᵀ ≡ Πₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ)
Π[] σ A B = refl -- holds definitionally

λₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm (Γ ▹ A) B) → Tm Γ (Πₚ A B)
λₚ {Γ} A B t = mkTm (λ γ a → t .t-el (Σᵤ-pair Γ A γ a))
                    (λ γ₀ γ₁ γe a₀ a₁ ae → t .t-rel (Σᵤ-pair Γ A γ₀ a₀) (Σᵤ-pair Γ A γ₁ a₁) (mkΣ γe ae))
                    (λ γ a → t .t-refl (Σᵤ-pair Γ A γ a))

λ[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm (Γ ▹ A) B) → (λₚ A B t) [ σ ]ᵗ ≡ λₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ) (t [ ↑ σ A ]ᵗ)
λ[] σ A B t = refl -- holds definitionally

appₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ (Πₚ A B)) (u : Tm Γ A) → Tm Γ (B [ sg A u ]ᵀ)
appₚ A B t u = mkTm (λ γ → t .t-el γ (tmApp A u γ))
                    (λ γ₀ γ₁ γe → t .t-rel γ₀ γ₁ γe (tmApp A u γ₀) (tmApp A u γ₁) (u .t-rel γ₀ γ₁ γe))
                    (λ γ → t .t-refl γ (tmApp A u γ))

app[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ (Πₚ A B)) (u : Tm Γ A)
        → (appₚ A B t u) [ σ ]ᵗ ≡ appₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ) (t [ σ ]ᵗ) (u [ σ ]ᵗ)
app[] σ A B t u = refl -- holds definitionally

Πβ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm (Γ ▹ A) B) (u : Tm Γ A) → appₚ A B (λₚ A B t) u ≡ t [ sg A u ]ᵗ
Πβ A B t u = refl -- holds definitionally

{- Remark that [Πη] only type-checks because we replaced [B] with [B [ pair (wk A) (var0 A) ]ᵀ].
   These two type families should be the same by the η law for substitutions, but this law only
   holds for closed substitutions. -}

Πη : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ (Πₚ A B))
   → t ≡ λₚ A (B [ pair (wk A) (var0 A) ]ᵀ) (appₚ (A [ wk A ]ᵀ) (B [ ↑ (wk A) A ]ᵀ) (t [ wk A ]ᵗ) (var0 A))
Πη A B t = refl -- holds definitionally

{- Next, we have (positive) Σ-types with β but without η. -}

Σₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty Γ
Σₚ A B = mkMorphism (λ γ → Σᵤ-el (setoidApp A γ) (partialApp U A B γ))
                    (λ γ₀ γ₁ γe → Σᵤ-rel (setoidApp A γ₀) (setoidApp A γ₁) (A .m-rel γ₀ γ₁ γe) (partialApp U A B γ₀) (partialApp U A B γ₁)
                                         (λ a₀ a₁ ae → m-rel B (Σᵤ-pair _ A γ₀ a₀) (Σᵤ-pair _ A γ₁ a₁) (mkΣ γe ae)))
                    (λ γ → Σᵤ-refl (setoidApp A γ) (partialApp U A B γ))

Σ[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) → (Σₚ A B) [ σ ]ᵀ ≡ Σₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ)
Σ[] σ A B = refl -- holds definitionally

pairₚ : {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ A) (u : Tm Γ (B [ sg A t ]ᵀ)) → Tm Γ (Σₚ A B)
pairₚ A B t u = mkTm (λ γ → mkΣ (tmApp A t γ) (u .t-el γ))
                     (λ γ₀ γ₁ γe → mkΣ (tmAppEq A t γe) (u .t-rel γ₀ γ₁ γe))
                     (λ γ → mk& refl (u .t-refl γ))

pair[] : {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) (t : Tm Γ A) (u : Tm Γ (B [ sg A t ]ᵀ))
       → (pairₚ A B t u) [ σ ]ᵗ ≡ pairₚ (A [ σ ]ᵀ) (B [ ↑ σ A ]ᵀ) (t [ σ ]ᵗ) (u [ σ ]ᵗ)
pair[] σ A B t u = refl -- holds definitionally

{- We should be able to define the positive eliminator for Σ, but it's really annoying to
   prove because of issues with η on substitutions -}
