{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import lib
open import setoids

module typeformers where

-- nat

ℕᵤ : SetoidPt U
ℕᵤ .p-el = mkU ℕ cℕ c₂ℕ c₃ℕ
ℕᵤ .p-rel = ★₁
ℕᵤ .p-refl = tt₁

-- embedding

Embᵤ : (P : Set) (eP : Lift₁ (P ↔ P)) → SetoidPt U
Embᵤ P eP .p-el = mkU P (cEmb P) (c₂Emb P) (c₃Emb P)
Embᵤ P eP .p-rel = eP -- mkLift₁ (equiv-refl P)
Embᵤ P eP .p-refl = tt₁ -- refl

-- dependent products

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

-- function application

Πᵤ-app-el : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (f : SetoidPt (El (Πᵤ A P))) (a : SetoidPt (El A)) → El (setoidApp P a) .s-el
Πᵤ-app-el A P f a = f .p-el a

Πᵤ-app-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (P₀ : SetoidMorphism (El A₀) U) (P₁ : SetoidMorphism (El A₁) U)
             (Pe : (a : SetoidPt (El A₀)) (b : SetoidPt (El A₁)) (eab : obseq-El A₀ A₁ a b) → SetoidEq (setoidApp P₀ a) (setoidApp P₁ b))
             (f₀ : SetoidPt (El (Πᵤ A₀ P₀))) (f₁ : SetoidPt (El (Πᵤ A₁ P₁))) (fe : obseq-El (Πᵤ A₀ P₀) (Πᵤ A₁ P₁) f₀ f₁)
             (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : obseq-El A₀ A₁ a₀ a₁)
             → El-eq (setoidApp P₀ a₀ .p-el .U-inU) (setoidApp P₁ a₁ .p-el .U-inU) (Πᵤ-app-el A₀ P₀ f₀ a₀) (Πᵤ-app-el A₁ P₁ f₁ a₁)
Πᵤ-app-rel A₀ A₁ Ae P₀ P₁ Pe f₀ f₁ fe a₀ a₁ ae = fe a₀ a₁ ae

Πᵤ-app-refl : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (f : SetoidPt (El (Πᵤ A P))) (a : SetoidPt (El A))
              → El-refl (setoidApp P a .p-el .U-inU₂) (Πᵤ-app-el A P f a) (Πᵤ-app-rel A A (A .p-rel) P P (P .m-rel) f f (f .p-rel) a a (a .p-rel))
Πᵤ-app-refl A P f a = f .p-refl a

Πᵤ-app : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (f : SetoidPt (El (Πᵤ A P))) (a : SetoidPt (El A)) → SetoidPt (El (setoidApp P a))
Πᵤ-app A P f a .p-el = Πᵤ-app-el A P f a
Πᵤ-app A P f a .p-rel = Πᵤ-app-rel A A (A .p-rel) P P (P .m-rel) f f (f .p-rel) a a (a .p-rel)
Πᵤ-app A P f a .p-refl = Πᵤ-app-refl A P f a

-- dependent sums

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

correctPair : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P))) → SetoidPt (El (Σᵤ A P))
correctPair A P x = mkPt (x .p-el) (mkΣ (x .p-el .fst .p-rel) (x .p-rel .snd)) (mk& refl (x .p-refl .snd))

Σᵤ-lemma : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P)))
           → correctPair A P x ≡ x
Σᵤ-lemma A P x = SetoidPt-eq₂ (El (Σᵤ A P)) (transpᵢ (λ X → mkΣ (x .p-el .fst .p-rel) (x .p-rel .snd) ≡ mkΣ X (x .p-rel .snd)) (x .p-refl .fst) refl)
                              (mk& refl (x .p-refl .snd)) (x .p-refl)

-- first projection

Σᵤ-fst-el : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P))) → El A .s-el
Σᵤ-fst-el A P x = x .p-el .fst .p-el

Σᵤ-fst-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (P₀ : SetoidMorphism (El A₀) U) (P₁ : SetoidMorphism (El A₁) U)
             (Pe : (a : SetoidPt (El A₀)) (b : SetoidPt (El A₁)) (eab : obseq-El A₀ A₁ a b) → SetoidEq (setoidApp P₀ a) (setoidApp P₁ b))
             (x₀ : SetoidPt (El (Σᵤ A₀ P₀))) (x₁ : SetoidPt (El (Σᵤ A₁ P₁))) (xe : obseq-El (Σᵤ A₀ P₀) (Σᵤ A₁ P₁) x₀ x₁)
             → El-eq (A₀ .p-el .U-inU) (A₁ .p-el .U-inU) (Σᵤ-fst-el A₀ P₀ x₀) (Σᵤ-fst-el A₁ P₁ x₁)
Σᵤ-fst-rel A₀ A₁ Ae P₀ P₁ Pe x₀ x₁ xe = xe .fst

Σᵤ-fst-refl : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P)))
              → El-refl (A .p-el .U-inU₂) (Σᵤ-fst-el A P x) (Σᵤ-fst-rel A A (A .p-rel) P P (P .m-rel) x x (x .p-rel))
Σᵤ-fst-refl A P x = transpᵢ (El-refl (A .p-el .U-inU₂) (x .p-el .fst .p-el)) (x .p-refl .fst) (x .p-el .fst .p-refl)

Σᵤ-fst : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P))) → SetoidPt (El A)
Σᵤ-fst A P x = mkPt (Σᵤ-fst-el A P x) (Σᵤ-fst-rel A A (A .p-rel) P P (P .m-rel) x x (x .p-rel)) (Σᵤ-fst-refl A P x)

Σᵤ-fst-lemma : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P))) → x .p-el .fst ≡ Σᵤ-fst A P x
Σᵤ-fst-lemma A P x = SetoidPt-eq₂ (El A) (x .p-refl .fst) (x .p-el .fst .p-refl) (Σᵤ-fst-refl A P x)

-- second projection

Σᵤ-snd-el-aux : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P))) {a : SetoidPt (El A)} (ha : x .p-el .fst ≡ a) → El (setoidApp P a) .s-el 
Σᵤ-snd-el-aux A P x ha = transp (λ a → El (setoidApp P a) .s-el) ha (x .p-el .snd)

Σᵤ-snd-el : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P))) → El (setoidApp P (Σᵤ-fst A P x)) .s-el
Σᵤ-snd-el A P x = Σᵤ-snd-el-aux A P x (Σᵤ-fst-lemma A P x)

Σᵤ-snd-rel-aux : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (P₀ : SetoidMorphism (El A₀) U) (P₁ : SetoidMorphism (El A₁) U)
                 (Pe : (a : SetoidPt (El A₀)) (b : SetoidPt (El A₁)) (eab : obseq-El A₀ A₁ a b) → SetoidEq (setoidApp P₀ a) (setoidApp P₁ b))
                 (x₀ : SetoidPt (El (Σᵤ A₀ P₀))) (x₁ : SetoidPt (El (Σᵤ A₁ P₁))) (xe : obseq-El (Σᵤ A₀ P₀) (Σᵤ A₁ P₁) x₀ x₁)
                 {a₀ : SetoidPt (El A₀)} (ha₀ : x₀ .p-el .fst ≡ a₀) {a₁ : SetoidPt (El A₁)} (ha₁ : x₁ .p-el .fst ≡ a₁)
                 → El-eq (setoidApp P₀ a₀ .p-el .U-inU) (setoidApp P₁ a₁ .p-el .U-inU) (Σᵤ-snd-el-aux A₀ P₀ x₀ ha₀) (Σᵤ-snd-el-aux A₁ P₁ x₁ ha₁)
Σᵤ-snd-rel-aux A₀ A₁ Ae P₀ P₁ Pe x₀ x₁ xe ha₀ ha₁ =
  J₂ (λ X₁ E₁ X₂ E₂ → El-eq (setoidApp P₀ X₁ .p-el .U-inU) (setoidApp P₁ X₂ .p-el .U-inU) (Σᵤ-snd-el-aux A₀ P₀ x₀ E₁) (Σᵤ-snd-el-aux A₁ P₁ x₁ E₂)) ha₀ ha₁ (xe .snd)

Σᵤ-snd-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (P₀ : SetoidMorphism (El A₀) U) (P₁ : SetoidMorphism (El A₁) U)
             (Pe : (a : SetoidPt (El A₀)) (b : SetoidPt (El A₁)) (eab : obseq-El A₀ A₁ a b) → SetoidEq (setoidApp P₀ a) (setoidApp P₁ b))
             (x₀ : SetoidPt (El (Σᵤ A₀ P₀))) (x₁ : SetoidPt (El (Σᵤ A₁ P₁))) (xe : obseq-El (Σᵤ A₀ P₀) (Σᵤ A₁ P₁) x₀ x₁)
             → El-eq (setoidApp P₀ (Σᵤ-fst A₀ P₀ x₀) .p-el .U-inU) (setoidApp P₁ (Σᵤ-fst A₁ P₁ x₁) .p-el .U-inU) (Σᵤ-snd-el A₀ P₀ x₀) (Σᵤ-snd-el A₁ P₁ x₁)
Σᵤ-snd-rel A₀ A₁ Ae P₀ P₁ Pe x₀ x₁ xe = Σᵤ-snd-rel-aux A₀ A₁ Ae P₀ P₁ Pe x₀ x₁ xe (Σᵤ-fst-lemma A₀ P₀ x₀) (Σᵤ-fst-lemma A₁ P₁ x₁)

Σᵤ-snd-refl : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P)))
              → El-refl (setoidApp P (Σᵤ-fst A P x) .p-el .U-inU₂) (Σᵤ-snd-el A P x) (Σᵤ-snd-rel A A (A .p-rel) P P (P .m-rel) x x (x .p-rel))
Σᵤ-snd-refl A P x =
  Jᵢ (λ X E → El-refl (setoidApp P X .p-el .U-inU₂) (Σᵤ-snd-el-aux A P x E) (Σᵤ-snd-rel-aux A A (A .p-rel) P P (P .m-rel) x x (x .p-rel) E E))
     (Σᵤ-fst-lemma A P x) (x .p-refl .snd)

Σᵤ-snd : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (x : SetoidPt (El (Σᵤ A P))) → SetoidPt (El (setoidApp P (Σᵤ-fst A P x)))
Σᵤ-snd A P x .p-el = Σᵤ-snd-el A P x
Σᵤ-snd A P x .p-rel = Σᵤ-snd-rel A A (A .p-rel) P P (P .m-rel) x x (x .p-rel)
Σᵤ-snd A P x .p-refl = Σᵤ-snd-refl A P x

-- dependent pairs

Σᵤ-pair-el : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (a : SetoidPt (El A)) (p : SetoidPt (El (setoidApp P a))) → El (Σᵤ A P) .s-el
Σᵤ-pair-el A P a p = mkΣ a (p .p-el)

Σᵤ-pair-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (P₀ : SetoidMorphism (El A₀) U) (P₁ : SetoidMorphism (El A₁) U)
             (Pe : (a : SetoidPt (El A₀)) (b : SetoidPt (El A₁)) (eab : obseq-El A₀ A₁ a b) → SetoidEq (setoidApp P₀ a) (setoidApp P₁ b))
             (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : obseq-El A₀ A₁ a₀ a₁)
             (p₀ : SetoidPt (El (setoidApp P₀ a₀))) (p₁ : SetoidPt (El (setoidApp P₁ a₁))) (pe : obseq-El (setoidApp P₀ a₀) (setoidApp P₁ a₁) p₀ p₁)
             → El-eq (Σᵤ A₀ P₀ .p-el .U-inU) (Σᵤ A₁ P₁ .p-el .U-inU) (Σᵤ-pair-el A₀ P₀ a₀ p₀) (Σᵤ-pair-el A₁ P₁ a₁ p₁)
Σᵤ-pair-rel A₀ A₁ Ae P₀ P₁ Pe a₀ a₁ ae p₀ p₁ pe = mkΣ ae pe

Σᵤ-pair-refl : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (a : SetoidPt (El A)) (p : SetoidPt (El (setoidApp P a)))
               → El-refl (Σᵤ A P .p-el .U-inU₂) (Σᵤ-pair-el A P a p) (Σᵤ-pair-rel A A (A .p-rel) P P (P .m-rel) a a (a .p-rel) p p (p .p-rel))
Σᵤ-pair-refl A P a p = mk& refl (p .p-refl)

Σᵤ-pair : (A : SetoidPt U) (P : SetoidMorphism (El A) U) (a : SetoidPt (El A)) (p : SetoidPt (El (setoidApp P a))) → SetoidPt (El (Σᵤ A P))
Σᵤ-pair A P a p = mkPt (Σᵤ-pair-el A P a p) (Σᵤ-pair-rel A A (A .p-rel) P P (P .m-rel) a a (a .p-rel) p p (p .p-rel)) (Σᵤ-pair-refl A P a p)

-- Quotient types

SetoidRelation-eq : (A B : SetoidPt U) (R : SetoidRelation (El A)) (S : SetoidRelation (El B)) → Set
SetoidRelation-eq A B R S = (a₀ : SetoidPt (El A)) (b₀ : SetoidPt (El B)) (e₀ : obseq-El A B a₀ b₀)
                            (a₁ : SetoidPt (El A)) (b₁ : SetoidPt (El B)) (e₁ : obseq-El A B a₁ b₁) → R .r-el a₀ a₁ ↔ S .r-el b₀ b₁

ℚᵤ-el : (A : SetoidPt U) (R : SetoidRelation (El A)) → U .s-el
ℚᵤ-el A R = mkU _ _ _ (c₃ℚ (A .p-el .U-set) (A .p-el .U-inU) (A .p-el .U-inU₂) (A .p-el .U-inU₃) (R .r-el)) 

ℚᵤ-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (R₀ : SetoidRelation (El A₀)) (R₁ : SetoidRelation (El A₁)) (Re : SetoidRelation-eq A₀ A₁ R₀ R₁)
         → U .s-rel (ℚᵤ-el A₀ R₀) (ℚᵤ-el A₁ R₁)
ℚᵤ-rel A₀ A₁ Ae R₀ R₁ Re = mkΣ Ae Re

ℚᵤ-refl : (A : SetoidPt U) (R : SetoidRelation (El A)) → U .s-refl (ℚᵤ-el A R) (ℚᵤ-rel A A (A .p-rel) R R (R .r-rel))
ℚᵤ-refl A R = A .p-refl

ℚᵤ : (A : SetoidPt U) (R : SetoidRelation (El A)) → SetoidPt U
ℚᵤ A R = mkPt (ℚᵤ-el A R) (ℚᵤ-rel A A (A .p-rel) R R (R .r-rel)) (ℚᵤ-refl A R)

-- Lemma for rewriting

correctQuo : (A : SetoidPt U) (R : SetoidRelation (El A)) (x : SetoidPt (El (ℚᵤ A R))) → SetoidPt (El (ℚᵤ A R))
correctQuo A R x = mkPt (x .p-el) (mkQuoEq (x .p-el) (x .p-el) (x .p-el .p-rel) clo-refl clo-refl) (mkQuoEqRefl (x .p-el .p-refl))

ℚᵤ-lemma : (A : SetoidPt U) (R : SetoidRelation (El A)) (x : SetoidPt (El (ℚᵤ A R))) → correctQuo A R x ≡ x
ℚᵤ-lemma A R x = SetoidPt-eq₂ (El (ℚᵤ A R)) (aux x) (mkQuoEqRefl (x .p-el .p-refl)) (x .p-refl)
  where
    aux : (x : SetoidPt (El (ℚᵤ A R))) → mkQuoEq (x .p-el) (x .p-el) (x .p-el .p-rel) clo-refl clo-refl ≡ x .p-rel
    aux (mkPt x _ (mkQuoEqRefl r)) = refl

-- Introduction rule for quotient types

ℚᵤ-intro-el : (A : SetoidPt U) (R : SetoidRelation (El A)) (a : SetoidPt (El A)) → ℚᵤ-el A R .U-set
ℚᵤ-intro-el A R a = a

ℚᵤ-intro-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (R₀ : SetoidRelation (El A₀)) (R₁ : SetoidRelation (El A₁)) (Re : SetoidRelation-eq A₀ A₁ R₀ R₁)
               (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : obseq-El A₀ A₁ a₀ a₁)
               → El-eq (ℚᵤ A₀ R₀ .p-el .U-inU) (ℚᵤ A₁ R₁ .p-el .U-inU) (ℚᵤ-intro-el A₀ R₀ a₀) (ℚᵤ-intro-el A₁ R₁ a₁)
ℚᵤ-intro-rel A₀ A₁ Ae R₀ R₁ Re a₀ a₁ ae = mkQuoEq a₀ a₁ ae clo-refl clo-refl

ℚᵤ-intro-refl : (A : SetoidPt U) (R : SetoidRelation (El A)) (a : SetoidPt (El A))
                → El-refl (ℚᵤ A R .p-el .U-inU₂) (ℚᵤ-intro-el A R a) (ℚᵤ-intro-rel A A (A .p-rel) R R (R .r-rel) a a (a .p-rel))
ℚᵤ-intro-refl A R a = mkQuoEqRefl (a .p-refl)

ℚᵤ-intro : (A : SetoidPt U) (R : SetoidRelation (El A)) → SetoidMorphism (El A) (El (ℚᵤ A R))
ℚᵤ-intro A R = mkMorphism (ℚᵤ-intro-el A R) (ℚᵤ-intro-rel A A (A .p-rel) R R (R .r-rel)) (ℚᵤ-intro-refl A R)

-- Elimination rule for quotient types

_∘_ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Setoid ℓ₁} {B : Setoid ℓ₂} {C : Setoid ℓ₃} (f : SetoidMorphism B A) (g : SetoidMorphism C B) → SetoidMorphism C A
f ∘ g = mkMorphism (λ c → (f .m-el (setoidApp g c))) (λ c₀ c₁ ce → f .m-rel (setoidApp g c₀) (setoidApp g c₁) (g .m-rel c₀ c₁ ce)) (λ c → f .m-refl (setoidApp g c))

-- ℚᵤ-elim-el : (A : SetoidPt U) (R : SetoidRelation (El A)) (P : SetoidMorphism (El (ℚᵤ A R)) U) (Hq : SetoidPt (El (Πᵤ A (P ∘ ℚᵤ-intro A R))))
--              (Heq : (a₀ a₁ : SetoidPt (El A)) (ae : R .r-el a₀ a₁)
--                     → obseq-El (setoidApp (P ∘ ℚᵤ-intro A R) a₀) (setoidApp (P ∘ ℚᵤ-intro A R) a₁) (Πᵤ-app A (P ∘ ℚᵤ-intro A R) Hq a₀) (Πᵤ-app A (P ∘ ℚᵤ-intro A R) Hq a₁))
--              (x : SetoidPt (El (ℚᵤ A R))) → El (setoidApp P x) .s-el
-- ℚᵤ-elim-el A R P Hq Heq x = transp (λ (x : SetoidPt (El (ℚᵤ A R))) → El (setoidApp P x) .s-el) (ℚᵤ-lemma A R x) (Hq .p-el (x .p-el))

-- ℚᵤ-elim-rel : (A₀ A₁ : SetoidPt U) (Ae : SetoidEq A₀ A₁) (R₀ : SetoidRelation (El A₀)) (R₁ : SetoidRelation (El A₁)) (Re : SetoidRelation-eq A₀ A₁ R₀ R₁)
--               (P₀ : SetoidMorphism (El (ℚᵤ A₀ R₀)) U) (P₁ : SetoidMorphism (El (ℚᵤ A₁ R₁)) U)
--               (Pe : (a₀ : SetoidPt (El (ℚᵤ A₀ R₀))) (a₁ : SetoidPt (El (ℚᵤ A₁ R₁))) (ae : obseq-El (ℚᵤ A₀ R₀) (ℚᵤ A₁ R₁) a₀ a₁)
--                     → SetoidEq (setoidApp P₀ a₀) (setoidApp P₁ a₁))
--               (Hq₀ : SetoidPt (El (Πᵤ A₀ (P₀ ∘ ℚᵤ-intro A₀ R₀)))) (Hq₁ : SetoidPt (El (Πᵤ A₁ (P₁ ∘ ℚᵤ-intro A₁ R₁))))
--               (Hqe : (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : obseq-El A₀ A₁ a₀ a₁)
--                      → El-eq (setoidApp (P₀ ∘ ℚᵤ-intro A₀ R₀) a₀ .p-el .U-inU) (setoidApp (P₁ ∘ ℚᵤ-intro A₁ R₁) a₁ .p-el .U-inU) (Hq₀ .p-el a₀) (Hq₁ .p-el a₁))
--               (Heq₀ : (a₀ a₁ : SetoidPt (El A₀)) (ae : R₀ .r-el a₀ a₁)
--                     → obseq-El (setoidApp (P₀ ∘ ℚᵤ-intro A₀ R₀) a₀) (setoidApp (P₀ ∘ ℚᵤ-intro A₀ R₀) a₁)
--                                (Πᵤ-app A₀ (P₀ ∘ ℚᵤ-intro A₀ R₀) Hq₀ a₀) (Πᵤ-app A₀ (P₀ ∘ ℚᵤ-intro A₀ R₀) Hq₀ a₁))
--               (Heq₁ : (a₀ a₁ : SetoidPt (El A₁)) (ae : R₁ .r-el a₀ a₁)
--                     → obseq-El (setoidApp (P₁ ∘ ℚᵤ-intro A₁ R₁) a₀) (setoidApp (P₁ ∘ ℚᵤ-intro A₁ R₁) a₁)
--                                (Πᵤ-app A₁ (P₁ ∘ ℚᵤ-intro A₁ R₁) Hq₁ a₀) (Πᵤ-app A₁ (P₁ ∘ ℚᵤ-intro A₁ R₁) Hq₁ a₁))
--               (x₀ : SetoidPt (El (ℚᵤ A₀ R₀))) (x₁ : SetoidPt (El (ℚᵤ A₁ R₁))) (xe : obseq-El (ℚᵤ A₀ R₀) (ℚᵤ A₁ R₁) x₀ x₁)
--               → El-eq (setoidApp P₀ x₀ .p-el .U-inU) (setoidApp P₁ x₁ .p-el .U-inU) (ℚᵤ-elim-el A₀ R₀ P₀ Hq₀ Heq₀ x₀) (ℚᵤ-elim-el A₁ R₁ P₁ Hq₁ Heq₁ x₁)
-- ℚᵤ-elim-rel A₀ A₁ Ae R₀ R₁ Re P₀ P₁ Pe Hq₀ Hq₁ Hqe Heq₀ Heq₁ x₀ x₁ xe = {!!}
--   where
--     aux : (x₀ : SetoidPt (El (ℚᵤ A₀ R₀))) (x₁ : SetoidPt (El (ℚᵤ A₁ R₁))) (xe : obseq-El (ℚᵤ A₀ R₀) (ℚᵤ A₁ R₁) (correctQuo A₀ R₀ x₀) (correctQuo A₁ R₁ x₁))
--           → El-eq (setoidApp P₀ (correctQuo A₀ R₀ x₀) .p-el .U-inU) (setoidApp P₁ (correctQuo A₁ R₁ x₁) .p-el .U-inU)
--                   (ℚᵤ-elim-el A₀ R₀ P₀ Hq₀ Heq₀ (correctQuo A₀ R₀ x₀)) (ℚᵤ-elim-el A₁ R₁ P₁ Hq₁ Heq₁ (correctQuo A₁ R₁ x₁))
--     aux x₀ x₁ (mkQuoEq a'₀ a'₁ a'₀≡a'₁ a₀≡a'₀ a₁≡a'₁) = {!!}

