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
      eab = obseq-sym B A b a (cast-refl-aux B A vBA b)
    in cast-aux-el (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Πᵤ-app A P f a)
  cast-aux-el _ _ (v₂Σ A B vAB P Q vPQ) x =
    let
      a : SetoidPt (El A)
      a = Σᵤ-fst A P x

      b : SetoidPt (El B)
      b = mkPt (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel)) (cast-aux-refl A B vAB a)

      eab : obseq-El A B a b
      eab = cast-refl-aux A B vAB a
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
      eab₀ = obseq-sym B₀ A₀ b₀ a₀ (cast-refl-aux B₀ A₀ vBA₀ b₀)

      eab₁ : obseq-El A₁ B₁ a₁ b₁
      eab₁ = obseq-sym B₁ A₁ b₁ a₁ (cast-refl-aux B₁ A₁ vBA₁ b₁)
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
      eab₀ = cast-refl-aux A₀ B₀ vAB₀ a₀

      eab₁ : obseq-El A₁ B₁ a₁ b₁
      eab₁ = cast-refl-aux A₁ B₁ vAB₁ a₁
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
      eab = obseq-sym B A b a (cast-refl-aux B A vBA b)
    in cast-aux-refl (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Πᵤ-app A P f a)
  cast-aux-refl _ _ (v₂Σ A B vAB P Q vPQ) x =
    let
      a : SetoidPt (El A)
      a = Σᵤ-fst A P x

      b : SetoidPt (El B)
      b = mkPt (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel)) (cast-aux-refl A B vAB a)

      eab : obseq-El A B a b
      eab = cast-refl-aux A B vAB a
    in mk& refl (cast-aux-refl (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Σᵤ-snd A P x))

  cast-refl-aux : (A B : SetoidPt U) (vAB : U-view₂ A B) (a : SetoidPt (El A)) → El-eq (A .p-el .U-inU) (B .p-el .U-inU) (a .p-el) (cast-aux-el A B vAB a)
  cast-refl-aux _ _ v₂ℕ a = nateq-refl (a .p-el)
  cast-refl-aux _ _ (v₂Emb P eP Q eQ ePQ) a = ★
  cast-refl-aux _ _ (v₂Π A B vBA P Q vPQ) f a b eab =
    let
      a₀ : SetoidPt (El A)
      a₀ = mkPt (cast-aux-el B A vBA b) (cast-aux-rel B B (B .p-rel) A A (A .p-rel) vBA vBA b b (b .p-rel)) (cast-aux-refl B A vBA b)

      ea₀b : obseq-El A B a₀ b
      ea₀b = obseq-sym B A b a₀ (cast-refl-aux B A vBA b)

      e₀ : obseq-El A A a a₀
      e₀ = obseq-trans-aux B A vBA A (U-inview A) b a₀ a (cast-refl-aux B A vBA b) eab

      e₁ : obseq-El (setoidApp P a) (setoidApp P a₀) (Πᵤ-app A P f a) (Πᵤ-app A P f a₀)
      e₁ = f .p-rel a a₀ e₀

      q : SetoidPt (El (setoidApp Q b))
      q = mkPt (cast-aux-el (setoidApp P a₀) (setoidApp Q b) (vPQ a₀ b ea₀b) (Πᵤ-app A P f a₀))
               (cast-aux-rel (setoidApp P a₀) (setoidApp P a₀) (P .m-rel a₀ a₀ (a₀ .p-rel)) (setoidApp Q b) (setoidApp Q b) (Q .m-rel b b (b .p-rel))
                             (vPQ a₀ b ea₀b) (vPQ a₀ b ea₀b)
                             (Πᵤ-app A P f a₀) (Πᵤ-app A P f a₀) (Πᵤ-app-rel A A (A .p-rel) P P (P .m-rel) f f (f .p-rel) a₀ a₀ (a₀ .p-rel)))
               (cast-aux-refl (setoidApp P a₀) (setoidApp Q b) (vPQ a₀ b ea₀b) (Πᵤ-app A P f a₀))

      e₂ : obseq-El (setoidApp P a₀) (setoidApp Q b) (Πᵤ-app A P f a₀) q
      e₂ = cast-refl-aux (setoidApp P a₀) (setoidApp Q b) (vPQ a₀ b ea₀b) (Πᵤ-app A P f a₀)

    in obseq-trans-aux (setoidApp P a₀) (setoidApp Q b) (vPQ a₀ b ea₀b) (setoidApp P a) (U-inview (setoidApp P a)) (Πᵤ-app A P f a₀) q (Πᵤ-app A P f a) e₂ e₁
  cast-refl-aux _ _ (v₂Σ A B vAB P Q vPQ) x =
    let
      a : SetoidPt (El A)
      a = Σᵤ-fst A P (correctPair A P x)

      b : SetoidPt (El B)
      b = mkPt (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel)) (cast-aux-refl A B vAB a)

      eab : obseq-El A B a b
      eab = cast-refl-aux A B vAB a
    in transp (λ (x : SetoidPt (El (Σᵤ A P))) → El-eq (Σᵤ-el A P .U-inU) (Σᵤ-el B Q .U-inU) (x .p-el) (cast-aux-el _ _ (v₂Σ A B vAB P Q vPQ) x)) (Σᵤ-lemma A P x)
              (mkΣ eab (cast-refl-aux (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (Σᵤ-snd A P (correctPair A P x)))) 

  obseq-trans-aux : (A B : SetoidPt U) (vAB : U-view₂ A B) → ∀ (C : SetoidPt U) (vC : U-view C) a b c → obseq-El A B a b → obseq-El C A c a → obseq-El C B c b
  obseq-trans-aux _ _ v₂ℕ _ vℕ a b c eab eca = nateq-trans eca eab
  obseq-trans-aux _ _ (v₂Emb P eP Q eQ ePQ) _ (vEmb P₁ eP₁) a b c eab eca = ★
  obseq-trans-aux _ _ (v₂Π A B vBA P Q vPQ) _ (vΠ C vC R vR) f g h efg ehf c b ecb =
    let
      a : SetoidPt (El A)
      a = mkPt (cast-aux-el B A vBA b) (cast-aux-rel B B (B .p-rel) A A (A .p-rel) vBA vBA b b (b .p-rel)) (cast-aux-refl B A vBA b)

      eab : obseq-El A B a b
      eab = obseq-sym B A b a (cast-refl-aux B A vBA b)

      eca : obseq-El C A c a
      eca = obseq-trans-aux B A vBA C vC b a c (cast-refl-aux B A vBA b) ecb
    in obseq-trans-aux (setoidApp P a) (setoidApp Q b) (vPQ a b eab) (setoidApp R c)
                       (vR c) (Πᵤ-app A P f a) (Πᵤ-app B Q g b) (Πᵤ-app C R h c) (efg a b eab) (ehf c a eca)
  obseq-trans-aux _ _ (v₂Σ A B vAB P Q vPQ) _ (vΣ C vC R vR) x y z exy ezx =
    let
      a = Σᵤ-fst A P (correctPair A P x)
      b = Σᵤ-fst B Q (correctPair B Q y)
      c = Σᵤ-fst C R (correctPair C R z)
    in J₃ (λ (x : SetoidPt (El (Σᵤ A P))) _ (y : SetoidPt (El (Σᵤ B Q))) _ (z : SetoidPt (El (Σᵤ C R))) _
             → (exy : obseq-El (Σᵤ A P) (Σᵤ B Q) x y) (ezx : obseq-El (Σᵤ C R) (Σᵤ A P) z x) → obseq-El (Σᵤ C R) (Σᵤ B Q) z y)
          (Σᵤ-lemma A P x) (Σᵤ-lemma B Q y) (Σᵤ-lemma C R z)
          (λ exy ezx → mkΣ (obseq-trans-aux A B vAB C vC a b c (exy .fst) (ezx .fst))
                           (obseq-trans-aux (setoidApp P a) (setoidApp Q b) (vPQ a b (exy .fst)) (setoidApp R c) (vR c) (Σᵤ-snd A P (correctPair A P x))
                                            (Σᵤ-snd B Q (correctPair B Q y)) (Σᵤ-snd C R (correctPair C R z)) (exy .snd) (ezx .snd)))
          exy ezx

-- cast operator

cast-el : (A B : SetoidPt U) (eAB : SetoidEq A B) → SetoidPt (El A) → El B .s-el
cast-el A B eAB = cast-aux-el A B (U-inview₂ A B eAB)

cast-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (B₀ B₁ : SetoidPt U) (Be : SetoidEq B₀ B₁)
           (eAB₀ : SetoidEq A₀ B₀) (eAB₁ : SetoidEq A₁ B₁)
           (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : obseq-El A₀ A₁ a₀ a₁)
           → El-eq (B₀ .p-el .U-inU) (B₁ .p-el .U-inU) (cast-el A₀ B₀ eAB₀ a₀) (cast-el A₁ B₁ eAB₁ a₁)
cast-rel A₀ A₁ Ae B₀ B₁ Be eAB₀ eAB₁ = cast-aux-rel A₀ A₁ Ae B₀ B₁ Be (U-inview₂ A₀ B₀ eAB₀) (U-inview₂ A₁ B₁ eAB₁)

cast-refl : (A B : SetoidPt U) (eAB : SetoidEq A B) (a : SetoidPt (El A))
          → El-refl (B .p-el .U-inU₂) (cast-el A B eAB a) (cast-rel A A (A .p-rel) B B (B .p-rel) eAB eAB a a (a .p-rel))
cast-refl A B eAB = cast-aux-refl A B (U-inview₂ A B eAB)

cast : (A B : SetoidPt U) (eAB : SetoidEq A B) (a : SetoidPt (El A)) → SetoidPt (El B)
cast A B eAB a = mkPt (cast-el A B eAB a) (cast-rel A A (A .p-rel) B B (B .p-rel) eAB eAB a a (a .p-rel)) (cast-refl A B eAB a)

-- cast equality

cast-eq : (A B : SetoidPt U) (eAB : SetoidEq A B) (a : SetoidPt (El A)) → obseq-El A B a (cast A B eAB a)
cast-eq A B eAB a = cast-refl-aux A B (U-inview₂ A B eAB) a

-- transitivity of observational equality

obseq-trans : ∀ (A B : SetoidPt U) (eAB : SetoidEq A B) (C : SetoidPt U) a b c → obseq-El A B a b → obseq-El C A c a → obseq-El C B c b
obseq-trans A B eAB C = obseq-trans-aux A B (U-inview₂ A B eAB) C (U-inview C) 
