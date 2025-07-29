{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import lib
open import setoids

module views where

-- Since it is so annoying to do pattern-matching on points in the universe, we
-- associate these "views" to them, which are much easier to pattern-match.

data U-view : (A : SetoidPt U) → Set₁ where
  vℕ : U-view ℕᵤ
  vEmb : (P : Set) (eP : Lift₁ (P ↔ P)) → U-view (Embᵤ P eP)
  vΠ : (A : SetoidPt U) (Av : U-view A) (P : SetoidMorphism (El A) U) (vP : (a : SetoidPt (El A)) → U-view (setoidApp P a)) → U-view (Πᵤ A P)
  vΣ : (A : SetoidPt U) (Av : U-view A) (P : SetoidMorphism (El A) U) (vP : (a : SetoidPt (El A)) → U-view (setoidApp P a)) → U-view (Σᵤ A P)

U-inview-aux : (A : Set) (Au : inU A) (Av : inU₂ A Au) (Aw : inU₃ A Au Av) (Ax : U-eq Au Au) (Ay : U-refl Av Ax) → U-view (mkPt (mkU A Au Av Aw) Ax Ay)
U-inview-aux Πt Πu Πv (c₃Π A Au Av Aw P Pu Pv Pw) Π-rel Π-refl =
  let
    ptA = mkPt {X = U} (mkU A Au Av Aw) (Π-rel .fst) (Π-refl .fst)
    vA = U-inview-aux A Au Av Aw (Π-rel .fst) (Π-refl .fst) 
    ptP : SetoidMorphism (El ptA) U
    ptP = mkMorphism (λ a → mkU (P a) (Pu a) (Pv a) (Pw a)) (Π-rel .snd) (Π-refl .snd)
    vP : (a : SetoidPt (El ptA)) → U-view (setoidApp ptP a)
    vP a = U-inview-aux (P a) (Pu a) (Pv a) (Pw a) (Π-rel .snd a a (a .p-rel)) (Π-refl .snd a)
  in vΠ ptA vA ptP vP
U-inview-aux Σt Σu Σv (c₃Σ A Au Av Aw P Pu Pv Pw) Σ-rel Σ-refl =
  let
    ptA = mkPt {X = U} (mkU A Au Av Aw) (Σ-rel .fst) (Σ-refl .fst)
    vA = U-inview-aux A Au Av Aw (Σ-rel .fst) (Σ-refl .fst) 
    ptP : SetoidMorphism (El ptA) U
    ptP = mkMorphism (λ a → mkU (P a) (Pu a) (Pv a) (Pw a)) (Σ-rel .snd) (Σ-refl .snd)
    vP : (a : SetoidPt (El ptA)) → U-view (setoidApp ptP a)
    vP a = U-inview-aux (P a) (Pu a) (Pv a) (Pw a) (Σ-rel .snd a a (a .p-rel)) (Σ-refl .snd a)
  in vΣ ptA vA ptP vP
U-inview-aux A Au Av c₃ℕ Ax Ay = vℕ
U-inview-aux A Au Av (c₃Emb P) Ax Ay = vEmb P Ax --transp (λ X → U-view (mkPt (mkU A (cEmb A) (c₂Emb A) (c₃Emb A)) X tt₁)) (sym Ay) (vEmb P) Ay

U-inview : (A : SetoidPt U) → U-view A
U-inview (mkPt (mkU A Au Av Aw) A-rel A-refl) = U-inview-aux A Au Av Aw A-rel A-refl

obseq-refl : (A : SetoidPt U) (a : SetoidPt (El A)) → obseq-El A A a a
obseq-refl A a = a .p-rel

obseq-reflU : (A : SetoidPt U) → SetoidEq A A
obseq-reflU A = A .p-rel

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
  mkΣ (obseq-symU-aux A vA B vB (e .fst)) (λ b a eba → obseq-symU-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e. snd a b (obseq-sym B A b a eba)))
obseq-symU-aux _ (vΣ A vA P vP) _ (vΣ B vB Q vQ) e =
  mkΣ (obseq-symU-aux A vA B vB (e .fst)) (λ b a eba → obseq-symU-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e. snd a b (obseq-sym B A b a eba)))

obseq-symU : (A : SetoidPt U) (B : SetoidPt U) → SetoidEq A B → SetoidEq B A
obseq-symU A B e = obseq-symU-aux A (U-inview A) B (U-inview B) e

-- View for two equal points. Note the contravariance in the domain of Π.

data U-view₂ : (A B : SetoidPt U) → Set₁ where
  v₂ℕ : U-view₂ ℕᵤ ℕᵤ
  v₂Emb : (P : Set) (eP : Lift₁ (P ↔ P)) (Q : Set) (eQ : Lift₁ (Q ↔ Q)) (ePQ : Lift₁ (P ↔ Q)) → U-view₂ (Embᵤ P eP) (Embᵤ Q eQ)
  v₂Π : (A : SetoidPt U) (B : SetoidPt U) (vAB : U-view₂ B A)
        (P : SetoidMorphism (El A) U) (Q : SetoidMorphism (El B) U)
        (vPQ : (a : SetoidPt (El A)) (b : SetoidPt (El B)) (eab : obseq-El A B a b) → U-view₂ (setoidApp P a) (setoidApp Q b))
       → U-view₂ (Πᵤ A P) (Πᵤ B Q)
  v₂Σ : (A : SetoidPt U) (B : SetoidPt U) (vAB : U-view₂ A B) (P : SetoidMorphism (El A) U) (Q : SetoidMorphism (El B) U)
        (vPQ : (a : SetoidPt (El A)) (b : SetoidPt (El B)) (eab : obseq-El A B a b) → U-view₂ (setoidApp P a) (setoidApp Q b))
       → U-view₂ (Σᵤ A P) (Σᵤ B Q)

U-inview₂-aux : (A : SetoidPt U) (vA : U-view A) (B : SetoidPt U) (vB : U-view B) (e : SetoidEq A B) → U-view₂ A B
U-inview₂-aux A vℕ B vℕ e = v₂ℕ
U-inview₂-aux A (vEmb P eP) B (vEmb Q eQ) e = v₂Emb P eP Q eQ e
U-inview₂-aux _ (vΠ A vA P vP) _ (vΠ B vB Q vQ) e =
  v₂Π A B (U-inview₂-aux B vB A vA (obseq-symU A B (e .fst))) P Q (λ a b eab → U-inview₂-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e .snd a b eab))
U-inview₂-aux _ (vΣ A vA P vP) _ (vΣ B vB Q vQ) e =
  v₂Σ A B (U-inview₂-aux A vA B vB (e .fst)) P Q (λ a b eab → U-inview₂-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e .snd a b eab))

U-inview₂ : (A : SetoidPt U) (B : SetoidPt U) (e : SetoidEq A B) → U-view₂ A B
U-inview₂ A B e = U-inview₂-aux A (U-inview A) B (U-inview B) e

