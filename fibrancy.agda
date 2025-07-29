{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import lib
open import setoids
open import views

module fibrancy where

mutual
  cast-aux-el : (A B : SetoidPt U) (vAB : U-view₂ A B) → SetoidPt (El A) → El B .s-el
  cast-aux-el _ _ v₂ℕ a = a .p-el
  cast-aux-el _ _ (v₂Emb P eP Q eQ ePQ) a = ePQ .lift₁ .fst (a .p-el)
  cast-aux-el _ _ (v₂Π A B vBA P Q vPQ) f b =
    let
      a : SetoidPt (El A)
      a = mkPt (cast-aux-el B A vBA b) (cast-aux-rel B B (B .p-rel) A A (A .p-rel) vBA vBA b b (b .p-rel)) (cast-aux-refl B A vBA b)

      eab : obseq-El A B a b
      eab = {!!}
    in cast-aux-el (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Πᵤ-app A P f a)
  cast-aux-el _ _ (v₂Σ A B vAB P Q vPQ) x =
    let
      a : SetoidPt (El A)
      a = Σᵤ-fst A P x

      b : SetoidPt (El B)
      b = mkPt (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel)) (cast-aux-refl A B vAB a)

      eab : obseq-El A B a b
      eab = {!!}
    in mkΣ b (cast-aux-el (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Σᵤ-snd A P x))

  cast-aux-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (B₀ B₁ : SetoidPt U) (Be : SetoidEq B₀ B₁)
                 (vAB₀ : U-view₂ A₀ B₀) (vAB₁ : U-view₂ A₁ B₁)
                 (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : obseq-El A₀ A₁ a₀ a₁)
                 → El-eq (B₀ .p-el .U-inU) (B₁ .p-el .U-inU) (cast-aux-el A₀ B₀ vAB₀ a₀) (cast-aux-el A₁ B₁ vAB₁ a₁)
  cast-aux-rel _ _ Ae _ _ Be v₂ℕ v₂ℕ a₀ a₁ ae = ae
  cast-aux-rel _ _ Ae _ _ Be (v₂Emb P eP Q eQ ePQ) (v₂Emb P₁ eP₁ Q₁ eQ₁ ePQ₁) a₀ a₁ ae = ★
  cast-aux-rel _ _ ΠAPe _ _ ΠBQe (v₂Π A₀ B₀ vBA₀ P₀ Q₀ vPQ₀) (v₂Π A₁ B₁ vBA₁ P₁ Q₁ vPQ₁) f₀ f₁ fe b₀ b₁ be =
    let
      a₀ : SetoidPt (El A₀)
      a₀ = mkPt (cast-aux-el B₀ A₀ vBA₀ b₀) (cast-aux-rel B₀ B₀ (B₀ .p-rel) A₀ A₀ (A₀ .p-rel) vBA₀ vBA₀ b₀ b₀ (b₀ .p-rel)) (cast-aux-refl B₀ A₀ vBA₀ b₀)

      a₁ : SetoidPt (El A₁)
      a₁ = mkPt (cast-aux-el B₁ A₁ vBA₁ b₁) (cast-aux-rel B₁ B₁ (B₁ .p-rel) A₁ A₁ (A₁ .p-rel) vBA₁ vBA₁ b₁ b₁ (b₁ .p-rel)) (cast-aux-refl B₁ A₁ vBA₁ b₁)

      Be : SetoidEq B₀ B₁
      Be = ΠBQe .fst

      Ae : SetoidEq A₀ A₁
      Ae = ΠAPe .fst

      ae : obseq-El A₀ A₁ a₀ a₁
      ae = cast-aux-rel B₀ B₁ Be A₀ A₁ Ae vBA₀ vBA₁ b₀ b₁ be

      eab₀ : obseq-El A₀ B₀ a₀ b₀
      eab₀ = {!!}

      eab₁ : obseq-El A₁ B₁ a₁ b₁
      eab₁ = {!!}
    in cast-aux-rel (setoidApp P₀ a₀) (setoidApp P₁ a₁) (ΠAPe .snd a₀ a₁ ae) (setoidApp Q₀ b₀) (setoidApp Q₁ b₁) (ΠBQe .snd b₀ b₁ be)
                    (vPQ₀ a₀ b₀ eab₀) (vPQ₁ a₁ b₁ eab₁) (Πᵤ-app A₀ P₀ f₀ a₀) (Πᵤ-app A₁ P₁ f₁ a₁) (Πᵤ-app-rel A₀ A₁ Ae P₀ P₁ (ΠAPe .snd) f₀ f₁ fe a₀ a₁ ae)
  cast-aux-rel _ _ ΣAPe _ _ ΣBQe (v₂Σ A₀ B₀ vAB₀ P₀ Q₀ vPQ₀) (v₂Σ A₁ B₁ vAB₁ P₁ Q₁ vPQ₁) x₀ x₁ xe =
    let
      a₀ : SetoidPt (El A₀)
      a₀ = Σᵤ-fst A₀ P₀ x₀

      a₁ : SetoidPt (El A₁)
      a₁ = Σᵤ-fst A₁ P₁ x₁

      ae : obseq-El A₀ A₁ a₀ a₁
      ae = Σᵤ-fst-rel A₀ A₁ (ΣAPe .fst) P₀ P₁ (ΣAPe .snd) x₀ x₁ xe

      b₀ : SetoidPt (El B₀)
      b₀ = mkPt (cast-aux-el A₀ B₀ vAB₀ a₀) (cast-aux-rel A₀ A₀ (A₀ .p-rel) B₀ B₀ (B₀ .p-rel) vAB₀ vAB₀ a₀ a₀ (a₀ .p-rel)) (cast-aux-refl A₀ B₀ vAB₀ a₀)

      b₁ : SetoidPt (El B₁)
      b₁ = mkPt (cast-aux-el A₁ B₁ vAB₁ a₁) (cast-aux-rel A₁ A₁ (A₁ .p-rel) B₁ B₁ (B₁ .p-rel) vAB₁ vAB₁ a₁ a₁ (a₁ .p-rel)) (cast-aux-refl A₁ B₁ vAB₁ a₁)

      be : obseq-El B₀ B₁ b₀ b₁
      be = cast-aux-rel A₀ A₁ (ΣAPe .fst) B₀ B₁ (ΣBQe .fst) vAB₀ vAB₁ a₀ a₁ ae

      eab₀ : obseq-El A₀ B₀ a₀ b₀
      eab₀ = {!!}

      eab₁ : obseq-El A₁ B₁ a₁ b₁
      eab₁ = {!!}
    in mkΣ be (cast-aux-rel (setoidApp P₀ a₀) (setoidApp P₁ a₁) (ΣAPe .snd a₀ a₁ ae) (setoidApp Q₀ b₀) (setoidApp Q₁ b₁) (ΣBQe .snd b₀ b₁ be)
                            (vPQ₀ a₀ b₀ eab₀) (vPQ₁ a₁ b₁ eab₁) (Σᵤ-snd A₀ P₀ x₀) (Σᵤ-snd A₁ P₁ x₁) (Σᵤ-snd-rel A₀ A₁ (ΣAPe .fst) P₀ P₁ (ΣAPe .snd) x₀ x₁ xe))

  cast-aux-refl : (A B : SetoidPt U) (vAB : U-view₂ A B) (a : SetoidPt (El A))
                  → El-refl (B .p-el .U-inU₂) (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel))
  cast-aux-refl _ _ v₂ℕ a = tt
  cast-aux-refl _ _ (v₂Emb P eP Q eQ ePQ) a = tt
  cast-aux-refl _ _ (v₂Π A B vBA P Q vPQ) f b =
    let
      a : SetoidPt (El A)
      a = mkPt (cast-aux-el B A vBA b) (cast-aux-rel B B (B .p-rel) A A (A .p-rel) vBA vBA b b (b .p-rel)) (cast-aux-refl B A vBA b)

      eab : obseq-El A B a b
      eab = {!!}
    in cast-aux-refl (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Πᵤ-app A P f a)
  cast-aux-refl _ _ (v₂Σ A B vAB P Q vPQ) x =
    let
      a : SetoidPt (El A)
      a = Σᵤ-fst A P x

      b : SetoidPt (El B)
      b = mkPt (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel)) (cast-aux-refl A B vAB a)

      eab : obseq-El A B a b
      eab = {!!}
    in mk& refl (cast-aux-refl (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Σᵤ-snd A P x))
