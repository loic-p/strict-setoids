-- CATEGORY WITH FAMILIES

-- -- Category of contexts and substitutions

Con : Set₁
Con = Setoid lzero

Sub : Con → Con → Set
Sub Γ Δ = SetoidMorphism Γ Δ

id : (Γ : Con) → Sub Γ Γ
id Γ .m-el γ = γ .p-el
id Γ .m-rel γ₁ γ₂ γe = γe
id Γ .m-refl γ = γ .p-refl

_∘_ : {Γ Δ Θ : Con} (σ : Sub Δ Γ) (τ : Sub Θ Δ) → Sub Θ Γ
_∘_ σ τ .m-el θ = σ .m-el (setoidApp τ θ)
_∘_ σ τ .m-rel θ₁ θ₂ θe = σ .m-rel (setoidApp τ θ₁) (setoidApp τ θ₂) (τ .m-rel θ₁ θ₂ θe)
_∘_ σ τ .m-refl θ = σ .m-refl (setoidApp τ θ)

id-left : {Γ Δ : Con} (σ : Sub Δ Γ) → id Γ ∘ σ ≡ σ
id-left σ = refl

id-right : {Γ Δ : Con} (σ : Sub Δ Γ) → σ ∘ id Δ ≡ σ
id-right σ = refl

assoc : {Γ Δ Θ Ξ : Con} (σ : Sub Δ Γ) (τ : Sub Θ Δ) (θ : Sub Ξ Θ) → σ ∘ (τ ∘ θ) ≡ (σ ∘ τ) ∘ θ
assoc σ τ θ = refl

-- Terminal object

◇ : Con
◇ .s-el = Unit
◇ .s-rel x y = Unit
◇ .s-refl x e = ⊤

ε : (Γ : Con) → Sub Γ ◇
ε Γ .m-el γ = ★
ε Γ .m-rel γ₁ γ₂ γe = ★
ε Γ .m-refl γ = tt

◇-η : {Γ : Con} (σ : Sub Γ ◇) → σ ≡ ε Γ
◇-η σ = refl

-- Presheaf of types

Ty : (Γ : Con) → Set₁
Ty Γ = DepSetoid Γ lzero

_[_]ᵀ : {Γ Δ : Con} (A : Ty Γ) (σ : Sub Δ Γ) → Ty Δ
_[_]ᵀ A σ .d-el δ = A .d-el (setoidApp σ δ)
_[_]ᵀ A σ .d-rel δ₁ a₁ δ₂ a₂ = A .d-rel (setoidApp σ δ₁) a₁ (setoidApp σ δ₂) a₂
_[_]ᵀ A σ .d-refl δ a ae = A .d-refl (setoidApp σ δ) a ae

[id]ᵀ : {Γ : Con} (A : Ty Γ) → A [ id Γ ]ᵀ ≡ A
[id]ᵀ A = refl

[∘]ᵀ : {Γ Δ Θ : Con} (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) → A [ σ ∘ τ ]ᵀ ≡ A [ σ ]ᵀ [ τ ]ᵀ
[∘]ᵀ A σ τ = refl

-- Dependent presheaf of terms

Tm : (Γ : Con) (A : Ty Γ) → Set
Tm Γ A = SetoidSection Γ A

_[_]ᵗ : {Γ Δ : Con} {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) → Tm Δ (A [ σ ]ᵀ)
_[_]ᵗ a σ .r-el δ = a .r-el (setoidApp σ δ)
_[_]ᵗ a σ .r-rel δ₁ δ₂ δe = a .r-rel (setoidApp σ δ₁) (setoidApp σ δ₂) (σ .m-rel δ₁ δ₂ δe)
_[_]ᵗ a σ .r-refl δ = a .r-refl (setoidApp σ δ)

[id]ᵗ : {Γ : Con} {A : Ty Γ} (a : Tm Γ A) → a [ id Γ ]ᵗ ≡ a
[id]ᵗ a = refl

[∘]ᵗ : {Γ Δ Θ : Con} {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) → a [ σ ∘ τ ]ᵗ ≡ a [ σ ]ᵗ [ τ ]ᵗ
[∘]ᵗ a σ τ = refl

-- Context extension

_▹_ : (Γ : Con) (A : Ty Γ) → Con
_▹_ Γ A = SetoidΣ Γ A

wk : {Γ : Con} (A : Ty Γ) → Sub (Γ ▹ A) Γ
wk {Γ} A .m-el x = x .p-el .fst .p-el
wk {Γ} A .m-rel x y e = e .fst
wk {Γ} A .m-refl x = transpᵢ (s-refl Γ (x .p-el .fst .p-el)) (x .p-refl .fst) (x .p-el .fst .p-refl)

wk-lemma : {Γ : Con} (A : Ty Γ) (x : SetoidPt (Γ ▹ A)) → x .p-el .fst ≡ setoidApp (wk A) x
wk-lemma {Γ} A x = SetoidPt-eq₂ Γ (x .p-refl .fst) (x .p-el .fst .p-refl) (setoidApp (wk A) x .p-refl)

var0 : {Γ : Con} (A : Ty Γ) → Tm (Γ ▹ A) (A [ wk A ]ᵀ)
var0 A .r-el x = transp (A .d-el) (wk-lemma A x) (x .p-el .snd)
var0 A .r-rel x y e = J₂ (λ X₁ E₁ X₂ E₂ → A .d-rel X₁ (transp (A .d-el) E₁ (x .p-el .snd)) X₂ (transp (A .d-el) E₂ (y .p-el .snd))) (wk-lemma A x) (wk-lemma A y) (e .snd) 
var0 A .r-refl x = {!x .p-el!}

pair : {Γ Δ : Con} (σ : Sub Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ σ ]ᵀ)) → Sub Δ (Γ ▹ A)
pair σ a .m-el δ = mkΣ (setoidApp σ δ) (a .r-el δ)
pair σ a .m-rel δ₁ δ₂ δe = mkΣ (σ .m-rel δ₁ δ₂ δe) (a .r-rel δ₁ δ₂ δe)
pair σ a .m-refl δ = {!!}

▹β₁ : {Γ Δ : Con} (σ : Sub Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ σ ]ᵀ)) → wk A ∘ pair σ a ≡ σ
▹β₁ σ a = refl

▹β₂ : {Γ Δ : Con} (σ : Sub Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ σ ]ᵀ)) → (var0 A) [ pair σ a ]ᵗ  ≡ a
▹β₂ σ a = refl
