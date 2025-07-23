{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import lib
open import setoids

module views where

-- Since it is so annoying to do pattern-matching on points in the universe, we
-- associate these "views" to them, which are much easier to pattern-match.

data U-view : (A : SetoidPt U) → Set₁ where
  vℕ : U-view ℕᵤ
  vEmb : (P : Set) → U-view (Embᵤ P)
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
U-inview-aux A Au Av (c₃Emb P) Ax Ay = transp (λ X → (H : X ≡ mkLift₁ (equiv-refl A)) → U-view (mkPt (mkU A (cEmb A) (c₂Emb A) (c₃Emb A)) X H)) (sym Ay) (λ H → vEmb P) Ay

U-inview : (A : SetoidPt U) → U-view A
U-inview (mkPt (mkU A Au Av Aw) A-rel A-refl) = U-inview-aux A Au Av Aw A-rel A-refl

-- View for two equal points. This way, we only have to pattern match against
-- four cases.

data U-view₂ : (A B : SetoidPt U) → Set₁ where
  v₂ℕ : U-view₂ ℕᵤ ℕᵤ
  v₂Emb : (P Q : Set) (e : Lift₁ (P ↔ Q)) → U-view₂ (Embᵤ P) (Embᵤ Q)
  v₂Π : (A : SetoidPt U) (B : SetoidPt U) (vAB : U-view₂ B A)
        (P : SetoidMorphism (El A) U) (Q : SetoidMorphism (El B) U)
        (vPQ : (a : SetoidPt (El A)) (b : SetoidPt (El B)) (eab : obseq-El A B a b) → U-view₂ (setoidApp P a) (setoidApp Q b))
       → U-view₂ (Πᵤ A P) (Πᵤ B Q)
  v₂Σ : (A : SetoidPt U) (B : SetoidPt U) (vAB : U-view₂ A B) (P : SetoidMorphism (El A) U) (Q : SetoidMorphism (El B) U)
        (vPQ : (a : SetoidPt (El A)) (b : SetoidPt (El B)) (eab : obseq-El A B a b) → U-view₂ (setoidApp P a) (setoidApp Q b))
       → U-view₂ (Σᵤ A P) (Σᵤ B Q)

U-inview₂-aux : (A : SetoidPt U) (vA : U-view A) (B : SetoidPt U) (vB : U-view B) (e : SetoidEq A B) → U-view₂ A B
U-inview₂-aux A vℕ B vℕ e = v₂ℕ
U-inview₂-aux A (vEmb P) B (vEmb Q) e = v₂Emb P Q e
U-inview₂-aux _ (vΠ A vA P vP) _ (vΠ B vB Q vQ) e =
  v₂Π A B (U-inview₂-aux B vB A vA (e .fst)) P Q (λ a b eab → U-inview₂-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e .snd a b eab))
U-inview₂-aux _ (vΣ A vA P vP) _ (vΣ B vB Q vQ) e =
  v₂Σ A B (U-inview₂-aux A vA B vB (e .fst)) P Q (λ a b eab → U-inview₂-aux (setoidApp P a) (vP a) (setoidApp Q b) (vQ b) (e .snd a b eab))

U-inview₂ : (A : SetoidPt U) (B : SetoidPt U) (e : SetoidEq A B) → U-view₂ A B
U-inview₂ A B e = U-inview₂-aux A (U-inview A) B (U-inview B) e

