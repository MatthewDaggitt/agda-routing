open import Algebra using (Semiring)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Fin using (Fin; zero; suc; _≟_; inject₁; fromℕ; punchOut)
open import Data.Fin.Properties using (any?; suc-injective)
open import Data.Vec using (Vec; _∷_; []; _++_; [_];  head; tail; lookup; map; tabulate)
open import Data.Vec.Properties using (∷-injectiveʳ)
open import Data.Product using (∃₂; _×_; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import RoutingLib.Data.Table using (foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Function

module db716.Algebra.Convergence where

module _ {c ℓ} (S : Semiring c ℓ) where
  open Semiring S

  pow : ℕ → Carrier → Carrier
  pow 0 s = 1#
  pow (suc 0) s = s
  pow (suc n) s = s * (pow n s)

  q-closure : ℕ → Carrier → Carrier
  q-closure zero s = 1#
  q-closure (suc n) s = (q-closure n s) + (pow (suc n) s)

  q-stable-element : ℕ → Carrier → Set _
  q-stable-element n s = q-closure (suc n) s ≈ q-closure n s

module _ where
  open Semiring

  q-stable : ∀ {c ℓ} → ℕ → Semiring c ℓ → Set _
  q-stable {c} {ℓ} n S = ∀ (s : Carrier S) → q-stable-element S n s

module _ {c ℓ} (S : Semiring c ℓ) where
  open import db716.Algebra.SemiringMatrix S
  open Semiring S
  open import db716.Algebra.Properties.Summation S
  open import Relation.Binary.EqReasoning setoid

  private ∏ = foldr _*_ 1#  
  
  ∏' : ∀ {n k : ℕ} → Mat n → Fin n → Fin n → Vec (Fin n) k  → Carrier
  ∏' {zero} _ _ _ _  = 0#
  ∏' {suc n} {suc k} M i j (l ∷ ls) = M i l * (∏' M l j ls)
  ∏' {suc n} {zero} M i j [] = M i j

  

  lemma1 : ∀ {n : ℕ} (M : Mat (suc n)) (k : ℕ) (i j : Fin (suc n)) → pow (SemiringMat (suc n)) (suc k) M i j ≈ ∑⋯∑ {suc n} {k} (∏' M i j)
  lemma1 M ℕ.zero i j = refl
  lemma1 {n} M (suc k) i j = begin
    pow (SemiringMat (suc n)) (suc (suc k)) M i j ≈⟨ refl ⟩
    ∑ (λ t → (M i t) * (pow 𝕄 (suc k) M t j))
      ≈⟨ ∑-cong {suc n} {λ t → M i t * pow 𝕄 (suc k) M t j} {λ t → M i t * ∑⋯∑ {suc n} {k} (∏' M t j)} (λ t → *-cong refl (lemma1 M k t j))  ⟩
    ∑ (λ t → (M i t) * ∑⋯∑ {suc n} {k} (∏' M t j))
      ≈⟨ ∑-cong {suc n} {λ t → (M i t) * ∑⋯∑ {suc n} {k} (∏' M t j)} {λ t → ∑⋯∑ {suc n} {k} (λ l → M i t * ∏' M t j l)} (λ t → ∑⋯∑-distˡ {suc n} {k} (∏' M t j) (M i t))  ⟩
    ∑ (λ t → ∑⋯∑ {suc n} {k} (λ l → (M i t) * (∏' M t j l))) ≈⟨ refl ⟩
    ∑⋯∑ {suc n} {suc k} (∏' M i j) ∎
    where 𝕄 = SemiringMat (suc n)

  lemma2 : ∀ (a b c : Carrier) → q-stable 0 S →  a * b * c + a * c ≈ a * c
  lemma2 a b c q-stab = begin
    a * b * c + a * c ≈⟨ sym (distribʳ c (a * b) a) ⟩
    (a * b + a) * c ≈⟨ sym (*-cong (+-cong refl (*-identityʳ a) ) refl) ⟩
    (a * b + a * 1#) * c ≈⟨ sym (*-cong (distribˡ a b 1#) refl) ⟩
    (a * (b + 1#)) * c ≈⟨ (*-cong (*-cong refl (+-comm b 1#) ) refl) ⟩
    (a * (1# + b)) * c ≈⟨ *-cong (*-cong refl (q-stab b)) refl ⟩
    (a * 1#) * c ≈⟨ *-cong (*-identityʳ a) refl ⟩
    a * c ∎

  i≡j⇒Idᵢⱼ≡1 : ∀ {n i j} → i ≡ j → Id n i j ≡ 1#
  i≡j⇒Idᵢⱼ≡1 {n} {i} {j} i≡j with i ≟ j
  ... | yes _ = _≡_.refl
  ... | no i≢j = contradiction i≡j i≢j

  i≡j⇒M⁽ᵏ⁾ᵢⱼ≡1 : ∀ {n k M i j} → i ≡ j → q-stable 0 S → q-closure (SemiringMat (suc n)) k M i j ≈ 1#
  i≡j⇒M⁽ᵏ⁾ᵢⱼ≡1 {n} {ℕ.zero} i≡j _ = reflexive (i≡j⇒Idᵢⱼ≡1 i≡j)
  i≡j⇒M⁽ᵏ⁾ᵢⱼ≡1 {n} {suc k} {M} {i} {j} i≡j 0-stab = begin
    q-closure (SemiringMat (suc n)) k M i j + pow (SemiringMat (suc n)) (suc k) M i j
      ≈⟨ +-cong (i≡j⇒M⁽ᵏ⁾ᵢⱼ≡1 {n} {k} i≡j 0-stab) refl ⟩
    1# + pow (SemiringMat (suc n)) (suc k) M i j
      ≈⟨ 0-stab _ ⟩
    1# ∎

  --map[punchOut[0]]≡tail : punchOut
  

  vecPigeonhole : ∀ {m n} → m Data.Nat.< n → (v : Vec (Fin m) n) → ∃₂ λ i j → i ≢ j × lookup i v ≡ lookup j v
  vecPigeonhole (s≤s z≤n) (() ∷ _)
  vecPigeonhole (s≤s (s≤s m≤n)) (v ∷ vs) with any? (λ k → lookup Fin.zero (v ∷ vs) ≟ lookup (suc k) (v ∷ vs))
  ... | yes (j , v₀≡vⱼ) = Fin.zero , suc j , (λ()) , v₀≡vⱼ
  ... | no ∀ₖv₀≢vₖ₊₁ with vecPigeonhole (s≤s m≤n) (tabulate (λ k → punchOut (λ eq → ∀ₖv₀≢vₖ₊₁ (k , eq))))
  ...   | (i , j , i≢j , vᵢ≡vⱼ) = suc i , suc j , i≢j ∘ suc-injective , {!vᵢ≡vⱼ!}
         -- where lem : lookup i tabulate (λ k → punchOut (λ eq → ∀ₖv₀≢vₖ₊₁ (k , eq))) ≡

  lemma3 : ∀ {n : ℕ} → q-stable 0 S → (M : Mat (suc n)) → (i j : Fin (suc n)) →
    ∀ p → q-closure (SemiringMat (suc n)) n M i j + ∏' {suc n} {suc n} M i j p ≈ q-closure (SemiringMat (suc n)) n M i j
  lemma3 {n} 0-stab M i j p = {!!}


  {-lemma3 : ∀ {n : ℕ} → q-stable 0 S → (M : Mat (suc n)) → (i j : Fin (suc n)) →  ∑⋯∑ (∏' {suc n} {n} M i j) + ∑⋯∑ (∏' {suc n} {suc n} M i j) ≈ ∑⋯∑ (∏' {suc n} {n} M i j)
  lemma3 {zero} 0-stab M zero zero = begin
    M Fin.zero Fin.zero + (M Fin.zero Fin.zero * M Fin.zero Fin.zero + 0#)
      ≈⟨ +-cong (sym (*-identityʳ (M Fin.zero Fin.zero))) (+-identityʳ (M Fin.zero Fin.zero * M Fin.zero Fin.zero)) ⟩
    M Fin.zero Fin.zero * 1# + M Fin.zero Fin.zero * M Fin.zero Fin.zero
      ≈⟨ sym (distribˡ _ _ _) ⟩
    M Fin.zero Fin.zero * (1# + M Fin.zero Fin.zero)
      ≈⟨ *-cong refl (0-stab (M Fin.zero Fin.zero)) ⟩
    M Fin.zero Fin.zero * 1#
      ≈⟨ *-identityʳ (M Fin.zero Fin.zero) ⟩
    M Fin.zero Fin.zero ∎
  lemma3 {zero} 0-stab M zero (suc ())
  lemma3 {zero} 0-stab M (suc ())
  lemma3 {suc n} 0-stab M i j = {!!} begin
    ∑⋯∑ (λ v → M i Fin.zero * ∏' M Fin.zero j V)
    + (∑⋯∑ (λ v → M i (suc Fin.zero) * ∏' M (suc Fin.zero) j v) + ∑ (λ x → ∑⋯∑ (λ v → M i (suc (suc x)) * ∏' M (suc (suc x)) j v)))
    + ∑⋯∑ (λ v → M i Fin.zero * (M Fin.zero Fin.zero * ∏' M Fin.zero j v))
    + (∑⋯∑ (λ v → M i Fin.zero * (M Fin.zero Fin.zero * ∏' M Fin.zero j v))-}
  

  thm : ∀ (n : ℕ) → q-stable 0 S → q-stable n (SemiringMat n)
  {-thm ℕ.zero 0-stab M Fin.zero Fin.zero = 0-stab (M Fin.zero Fin.zero)
  thm ℕ.zero 0-stab M Fin.zero (suc ())
  thm ℕ.zero 0-stab M (suc ())
  thm (n) 0-stab M i j with i ≟ j
  ... | yes i≡j = trans (i≡j⇒M⁽ᵏ⁾ᵢⱼ≡1 {n} {suc n} i≡j 0-stab) (sym (i≡j⇒M⁽ᵏ⁾ᵢⱼ≡1 {n} {n} i≡j 0-stab)) 
  ... | no i≢j = -}
  {-thm (suc n) 0-stab M i j = begin
    q-closure (SemiringMat (suc (suc n))) (n) M i j + pow (SemiringMat (suc (suc n))) (suc (suc n)) M i j
      ≈⟨ +-cong refl {!lemma1 {n} M n i j!} ⟩
    q-closure (SemiringMat (suc (suc n))) n M i j + ∑⋯∑ {suc (suc n)} {suc n} (∏' M i j)
      ≈⟨ {!!} ⟩
    {!!} ∎-}
  thm zero _ _ ()
  thm (suc n) 0-stab M i j = begin
    q-closure (SemiringMat (suc n)) (suc n) M i j + pow (SemiringMat (suc n)) (suc (suc n)) M i j
      ≈⟨ +-cong {_} {_} {pow (SemiringMat (suc n)) (suc (suc n)) M i j} {∑⋯∑ {suc n} {suc n} (∏' M i j)} refl (lemma1 {n} M (suc n) i j) ⟩
    q-closure (SemiringMat (suc n)) (suc n) M i j + ∑⋯∑ {suc n} {suc n} (∏' M i j)
      ≈⟨ {!!} ⟩
    {!!} ∎
    
