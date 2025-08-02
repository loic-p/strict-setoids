{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import lib
open import setoids
open import typeformers
open import views

module fibrancy where

-- Some lemmas on closures for quotients

clo-snoc : {ℓ : Level} (A : Setoid ℓ) (R : (a b : SetoidPt A) → Set ℓ) {a b c : SetoidPt A} → R a b → closure A R b c → closure A R a c
clo-snoc A R r clo-refl = clo-cons _ _ r (clo-refl)
clo-snoc A R r (clo-cons c d r' e) = clo-cons c d r' (clo-snoc A R r e)
clo-snoc A R r (clo-anticons c d r' e) = clo-anticons c d r' (clo-snoc A R r e)

clo-antisnoc : {ℓ : Level} (A : Setoid ℓ) (R : (a b : SetoidPt A) → Set ℓ) {a b c : SetoidPt A} → R b a → closure A R b c → closure A R a c
clo-antisnoc A R r clo-refl = clo-anticons _ _ r clo-refl
clo-antisnoc A R r (clo-cons c d r' e) = clo-cons c d r' (clo-antisnoc A R r e)
clo-antisnoc A R r (clo-anticons c d r' e) = clo-anticons c d r' (clo-antisnoc A R r e)

closure-sym : {ℓ : Level} (A : Setoid ℓ) (R : (a b : SetoidPt A) → Set ℓ) {a b : SetoidPt A} → closure A R a b → closure A R b a
closure-sym A R clo-refl = clo-refl
closure-sym A R (clo-cons b c r e) = clo-antisnoc A R r (closure-sym A R e)
closure-sym A R (clo-anticons b c r e) = clo-snoc A R r (closure-sym A R e)

closure-trans : {ℓ : Level} (A : Setoid ℓ) (R : (a b : SetoidPt A) → Set ℓ) {a b c : SetoidPt A} → closure A R a b → closure A R b c → closure A R a c
closure-trans A R e clo-refl = e
closure-trans A R e (clo-cons c d r f) = clo-cons c d r (closure-trans A R e f)
closure-trans A R e (clo-anticons c d r f) = clo-anticons c d r (closure-trans A R e f)

closure-cast : (A B : SetoidPt U) (cast : SetoidPt (El A) → SetoidPt (El B)) (cast-eq : (a : SetoidPt (El A)) → obseq-El A B a (cast a))
               (R : SetoidRelation (El A)) (S : SetoidRelation (El B))
               (eRS : (a₀ : SetoidPt (El A)) (b₀ : SetoidPt (El B)) (e₀ : obseq-El A B a₀ b₀)
                      (a₁ : SetoidPt (El A)) (b₁ : SetoidPt (El B)) (e₁ : obseq-El A B a₁ b₁) → R .r-el a₀ a₁ ↔ S .r-el b₀ b₁)
               (a a' : SetoidPt (El A)) → closure (El A) (R .r-el) a a' → closure (El B) (S .r-el) (cast a) (cast a')
closure-cast A B cast cast-eq R S eRS a a' clo-refl = clo-refl
closure-cast A B cast cast-eq R S eRS a a' (clo-cons b .a' x e) =
  clo-cons (cast b) (cast a') (eRS b (cast b) (cast-eq b) a' (cast a') (cast-eq a') .fst x) (closure-cast A B cast cast-eq R S eRS a b e)
closure-cast A B cast cast-eq R S eRS a a' (clo-anticons b .a' x e) =
  clo-anticons (cast b) (cast a') (eRS a' (cast a') (cast-eq a') b (cast b) (cast-eq b) .fst x) (closure-cast A B cast cast-eq R S eRS a b e)

-- Now we can define "fibrancy structures" (that is, cast and transitivity) with a big mutual induction on types

mutual
  cast-aux-el : (A B : SetoidPt U) (vAB : U-view₂ A B) → SetoidPt (El A) → El B .s-el
  cast-aux-el _ _ v₂ℕ a = a .p-el
  cast-aux-el _ _ (v₂ℚ A B vAB R S eRS) a =
    mkPt (cast-aux-el A B vAB (a .p-el)) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB (a .p-el) (a .p-el) (a .p-el .p-rel)) (cast-aux-refl A B vAB (a .p-el))
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
  cast-aux-rel _ _ ℚAe _ _ ℚBe (v₂ℚ A₀ B₀ vAB₀ R₀ S₀ eRS₀) (v₂ℚ A₁ B₁ vAB₁ R₁ S₁ eRS₁) x₀ x₁ xe =
    let
      a₀ = x₀ .p-el
      a'₀ = xe .qe-a'
      a₁ = x₁ .p-el
      a'₁ = xe .qe-b'

      cast₀ : SetoidPt (El A₀) → SetoidPt (El B₀)
      cast₀ a₀ = mkPt (cast-aux-el A₀ B₀ vAB₀ a₀) (cast-aux-rel A₀ A₀ (A₀ .p-rel) B₀ B₀ (B₀ .p-rel) vAB₀ vAB₀ a₀ a₀ (a₀ .p-rel)) (cast-aux-refl A₀ B₀ vAB₀ a₀)
      cast₁ : SetoidPt (El A₁) → SetoidPt (El B₁)
      cast₁ a₁ = mkPt (cast-aux-el A₁ B₁ vAB₁ a₁) (cast-aux-rel A₁ A₁ (A₁ .p-rel) B₁ B₁ (B₁ .p-rel) vAB₁ vAB₁ a₁ a₁ (a₁ .p-rel)) (cast-aux-refl A₁ B₁ vAB₁ a₁)

      b₀ = cast₀ a₀
      b'₀ = cast₀ a'₀
      b₁ = cast₁ a₁
      b'₁ = cast₁ a'₁

      be : obseq-El B₀ B₁ b'₀ b'₁
      be = cast-aux-rel A₀ A₁ (ℚAe .fst) B₀ B₁ (ℚBe .fst) vAB₀ vAB₁ a'₀ a'₁ (xe .qe-a'≡b')
    in mkQuoEq b'₀ b'₁ be (closure-cast A₀ B₀ cast₀ (cast-refl-aux A₀ B₀ vAB₀) R₀ S₀ eRS₀ a₀ a'₀ (xe .qe-a≡a'))
               (closure-cast A₁ B₁ cast₁ (cast-refl-aux A₁ B₁ vAB₁) R₁ S₁ eRS₁ a₁ a'₁ (xe .qe-b≡b'))
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
  cast-aux-refl _ _ (v₂ℚ A B vAB R S eRS) (mkPt a _ (mkQuoEqRefl r)) = mkQuoEqRefl (cast-aux-refl A B vAB a)
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
  cast-refl-aux _ _ (v₂ℚ A B vAB R S eRS) a =
    let
      cast : SetoidPt (El A) → SetoidPt (El B)
      cast a = mkPt (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel)) (cast-aux-refl A B vAB a)
    in mkQuoEq (a .p-el) (cast (a .p-el)) (cast-refl-aux A B vAB (a .p-el)) clo-refl clo-refl
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
  obseq-trans-aux _ _ (v₂ℚ A B vAB R S eRS) _ (vℚ C vC T) a b c eab eca = aux (closure-sym (El A) (R .r-el) r₀)
    where -- this one is somewhat annoying, we have to case split on whether some equalities (obtained via closure) are reflexivity or not
      cast : SetoidPt (El A) → SetoidPt (El B)
      cast a = mkPt (cast-aux-el A B vAB a) (cast-aux-rel A A (A .p-rel) B B (B .p-rel) vAB vAB a a (a .p-rel)) (cast-aux-refl A B vAB a)

      a' = eab .qe-a'
      b' = eab .qe-b'
      c' = eca .qe-a'
      a″ = eca .qe-b'
      b″ = cast a″

      r₀ : closure (El A) (R .r-el) a' a″
      r₀ = closure-trans (El A) (R .r-el) (closure-sym (El A) (R .r-el) (eab .qe-a≡a')) (eca .qe-b≡b')

      aux : closure (El A) (R .r-el) a″ a' → obseq-El (ℚᵤ C T) (ℚᵤ B S) c b
      aux clo-refl = mkQuoEq c' b' (obseq-trans-aux A B vAB C vC a' b' c' (eab .qe-a'≡b') (eca .qe-a'≡b')) (eca .qe-a≡a') (eab .qe-b≡b')
      aux (clo-cons a‴ .a' x r) =
        mkQuoEq c' b″ (obseq-trans-aux A B vAB C vC a″ b″ c' (cast-refl-aux A B vAB a″) (eca .qe-a'≡b')) (eca .qe-a≡a')
                (closure-trans (El B) (S .r-el) (eab .qe-b≡b')
                               (clo-antisnoc (El B) (S .r-el) (eRS a‴ (cast a‴) (cast-refl-aux A B vAB a‴) a' b' (eab .qe-a'≡b') .fst x)
                                             (closure-cast A B cast (cast-refl-aux A B vAB) R S eRS a‴ a″ (closure-sym (El A) (R .r-el) r))))
      aux (clo-anticons a‴ .a' x r) = 
        mkQuoEq c' b″ (obseq-trans-aux A B vAB C vC a″ b″ c' (cast-refl-aux A B vAB a″) (eca .qe-a'≡b')) (eca .qe-a≡a')
                (closure-trans (El B) (S .r-el) (eab .qe-b≡b')
                               ( clo-snoc (El B) (S .r-el) (eRS a' b' (eab .qe-a'≡b') a‴ (cast a‴) (cast-refl-aux A B vAB a‴) .fst x)
                                          (closure-cast A B cast (cast-refl-aux A B vAB) R S eRS a‴ a″ (closure-sym (El A) (R .r-el) r)) ))
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

-- transitivity on universe

obseq-transU-aux : (A B C : SetoidPt U) (vA : U-view A) (vB : U-view B) (vC : U-view C) (eAB : SetoidEq A B) (eCA : SetoidEq C A) → SetoidEq C B
obseq-transU-aux _ _ _ vℕ vℕ vℕ eAB eCA = ★₁
obseq-transU-aux _ _ _ (vℚ A vA R) (vℚ B vB S) (vℚ C vC T) eAB eCA =
  mkΣ (obseq-transU-aux A B C vA vB vC (eAB .fst) (eCA .fst))
      (λ c₀ b₀ ecb₀ c₁ b₁ ecb₁ →
        let
          a₀ = cast C A (eCA .fst) c₀
          a₁ = cast C A (eCA .fst) c₁
          eca₀ = cast-eq C A (eCA .fst) c₀
          eca₁ = cast-eq C A (eCA .fst) c₁
          eab₀ = obseq-sym B A b₀ a₀ (obseq-trans C A (eCA .fst) B c₀ a₀ b₀ eca₀ (obseq-sym C B c₀ b₀ ecb₀))
          eab₁ = obseq-sym B A b₁ a₁ (obseq-trans C A (eCA .fst) B c₁ a₁ b₁ eca₁ (obseq-sym C B c₁ b₁ ecb₁))
        in equiv-trans (eCA .snd c₀ a₀ eca₀ c₁ a₁ eca₁) (eAB .snd a₀ b₀ eab₀ a₁ b₁ eab₁))
obseq-transU-aux _ _ _ (vEmb P eP) (vEmb P₁ eP₁) (vEmb P₂ eP₂) eAB eCA = mkLift₁ (equiv-trans (eCA .lift₁) (eAB .lift₁))
obseq-transU-aux _ _ _ (vΠ A vA P vP) (vΠ B vB Q vQ) (vΠ C vC R vR) e f =
  mkΣ (obseq-transU-aux A B C vA vB vC (e .fst) (f .fst))
      (λ c b ecb →
        let
          a = cast C A (f .fst) c
          eca = cast-eq C A (f .fst) c
          eab = obseq-sym B A b a (obseq-trans C A (f .fst) B c a b eca (obseq-sym C B c b ecb))
        in obseq-transU-aux (setoidApp P a) (setoidApp Q b) (setoidApp R c) (vP a) (vQ b) (vR c) (e .snd a b eab) (f .snd c a eca)) 
obseq-transU-aux _ _ _ (vΣ A vA P vP) (vΣ B vB Q vQ) (vΣ C vC R vR) e f =
  mkΣ (obseq-transU-aux A B C vA vB vC (e .fst) (f .fst))
      (λ c b ecb →
        let
          a = cast C A (f .fst) c
          eca = cast-eq C A (f .fst) c
          eab = obseq-sym B A b a (obseq-trans C A (f .fst) B c a b eca (obseq-sym C B c b ecb))
        in obseq-transU-aux (setoidApp P a) (setoidApp Q b) (setoidApp R c) (vP a) (vQ b) (vR c) (e .snd a b eab) (f .snd c a eca)) 

obseq-transU : (A B C : SetoidPt U) (eAB : SetoidEq A B) (eCA : SetoidEq C A) → SetoidEq C B
obseq-transU A B C = obseq-transU-aux A B C (U-inview A) (U-inview B) (U-inview C)
