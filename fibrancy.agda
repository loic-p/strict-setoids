{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import lib
open import setoids
open import views

module fibrancy where

obseq-sym-aux : (A : SetoidPt U) (vA : U-view A) (B : SetoidPt U) (vB : U-view B) (a : SetoidPt (El A)) (b : SetoidPt (El B)) → obseq-El A B a b → obseq-El B A b a
obseq-sym-aux _ vℕ _ vℕ a b e = nateq-sym e
obseq-sym-aux _ (vEmb P eP) _ (vEmb Q eQ) a b e = ★
obseq-sym-aux _ (vΠ A vA P vP) _ (vΠ B vB Q vQ) f g efg b a eba =
  obseq-sym-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (Πᵤ-app A P f a) (Πᵤ-app B Q g b) (efg a b (obseq-sym-aux B vB A vA b a eba)) 
obseq-sym-aux _ (vΣ A vA P vP) _ (vΣ B vB Q vQ) x y e =
  J₂ (λ x _ y _ → obseq-El (Σᵤ B Q) (Σᵤ A P) y x) (Σᵤ-lemma A P x) (Σᵤ-lemma B Q y)
     (mkΣ (obseq-sym-aux A vA B vB (Σᵤ-fst A P (correctPair A P x)) (Σᵤ-fst B Q (correctPair B Q y)) (e .fst))
          (obseq-sym-aux (setoidApp P (Σᵤ-fst A P (correctPair A P x))) (vP (Σᵤ-fst A P (correctPair A P x)))
                         (setoidApp Q (Σᵤ-fst B Q (correctPair B Q y))) (vQ (Σᵤ-fst B Q (correctPair B Q y)))
                         (Σᵤ-snd A P (correctPair A P x)) (Σᵤ-snd B Q (correctPair B Q y)) (e .snd))) 

obseq-sym : (A B : SetoidPt U) (a : SetoidPt (El A)) (b : SetoidPt (El B)) → obseq-El A B a b → obseq-El B A b a
obseq-sym A B a b = obseq-sym-aux A (U-inview A) B (U-inview B) a b

obseq-symU-aux : (A : SetoidPt U) (vA : U-view A) (B : SetoidPt U) (vB : U-view B) → SetoidEq A B → SetoidEq B A
obseq-symU-aux _ vℕ _ vℕ e = ★₁
obseq-symU-aux _ (vEmb P eP) _ (vEmb Q eQ) e = mkLift₁ (equiv-sym (e .lift₁))
obseq-symU-aux _ (vΠ A vA P vP) _ (vΠ B vB Q vQ) e =
  mkΣ (obseq-symU-aux B vB A vA (e .fst)) (λ b a eba → obseq-symU-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e. snd a b (obseq-sym B A b a eba)))
obseq-symU-aux _ (vΣ A vA P vP) _ (vΣ B vB Q vQ) e =
  mkΣ (obseq-symU-aux A vA B vB (e .fst)) (λ b a eba → obseq-symU-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e. snd a b (obseq-sym B A b a eba)))

obseq-symU : (A : SetoidPt U) (B : SetoidPt U) → SetoidEq A B → SetoidEq B A
obseq-symU A B e = obseq-symU-aux A (U-inview A) B (U-inview B) e

-- obseq-rel-aux : (A₀ : SetoidPt U) (A₁ : SetoidPt U) (Av : U-view₂ A₀ A₁)
--             (B₀ : SetoidPt U) (B₁ : SetoidPt U) (Bv : U-view₂ B₀ B₁)
--             (a₀ : SetoidPt (El A₀)) (a₁ : SetoidPt (El A₁)) (ae : U* .d-rel A₀ (a₀ .p-el) A₁ (a₁ .p-el))
--             (b₀ : SetoidPt (El B₀)) (b₁ : SetoidPt (El B₁)) (be : U* .d-rel B₀ (b₀ .p-el) B₁ (b₁ .p-el))
--           → obseq-el A₀ B₀ a₀ b₀ ↔ obseq-el A₁ B₁ a₁ b₁
-- obseq-rel-aux _ _ v₂ℕ _ _ v₂ℕ a₀ a₁ ae b₀ b₁ be = {!ez!}
-- obseq-rel-aux _ _ v₂ℕ _ _ (v₂Emb P Q e) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ v₂ℕ _ _ (v₂Π A B vAB P Q vPQ) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ v₂ℕ _ _ (v₂Σ A B vAB P Q vPQ) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Emb P Q e) _ _ v₂ℕ a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Emb P Q e) _ _ (v₂Emb P₁ Q₁ e₁) a₀ a₁ ae b₀ b₁ be = equiv-refl Unit
-- obseq-rel-aux _ _ (v₂Emb P Q e) _ _ (v₂Π A B vAB P₁ Q₁ vPQ) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Emb P Q e) _ _ (v₂Σ A B vAB P₁ Q₁ vPQ) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Π A B vAB P Q vPQ) _ _ v₂ℕ a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Π A B vAB P Q vPQ) _ _ (v₂Emb P₁ Q₁ e) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Π A₀ A₁ vA P₀ P₁ vP) _ _ (v₂Π B₀ B₁ vB Q₀ Q₁ vQ) f₀ f₁ fe g₀ g₁ ge = {!nécessite cast, et va même nécessiter cast-on-refl!}
-- obseq-rel-aux _ _ (v₂Π A B vAB P Q vPQ) _ _ (v₂Σ A₂ B₂ vAB₁ P₁ Q₁ vPQ₁) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Σ A B vAB P Q vPQ) _ _ v₂ℕ a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Σ A B vAB P Q vPQ) _ _ (v₂Emb P₁ Q₁ e) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Σ A B vAB P Q vPQ) _ _ (v₂Π A₂ B₂ vAB₁ P₁ Q₁ vPQ₁) a₀ a₁ ae b₀ b₁ be = equiv-refl Empty
-- obseq-rel-aux _ _ (v₂Σ A B vAB P Q vPQ) _ _ (v₂Σ A₂ B₂ vAB₁ P₁ Q₁ vPQ₁) a₀ a₁ ae b₀ b₁ be = {!!}

