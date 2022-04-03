open import Data.Fin using (Fin)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Nat as ℕ using (ℕ; NonZero; zero; suc; z≤n; s≤s; _+_; _^_; _*_; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec using (_∷_)
open import Data.Unit using () renaming (⊤ to ⊤ᵤ)
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred) renaming (_∈_ to _∈ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Properties

module RoutingLib.Data.Fin.Subset.Induction where

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    n : ℕ

All : Pred (Fin n) ℓ → Subset n → Set ℓ
All P xs = ∀ {i} → i ∈ xs → P i

record OneByOneInduction (P : ℕ → Pred (Fin n) ℓ₁)
                         (Q : ℕ → Subset n → Pred (Fin n) ℓ₂)
                         : Set (ℓ₁ ⊔ ℓ₂) where
  field
    -- Given a subset, provides the next element to be added to it.
    next      : (t : ℕ) (s : Subset n) → Nonfull s → Fin n
    -- The next element is not in the subset
    next∉     : ∀ t s (nf : Nonfull s) → next t s nf ∉ s
    -- If all the elements within the subset satisfy P and all the elements outside of it satisfy Q
    -- then the next element for that subset will also satisfy P
    P[next]   : ∀ t s (nf : Nonfull s) → All (P t) s → All (Q t s) (∁ s) → next t s nf ∈ᵤ P (suc t)
    -- Everything is in Q initially
    ∈Q₀⊥      : ∀ i → i ∈ᵤ Q 0 ⊥
    -- The set P is increasing over time
    Pₜ⊆Pₜ₊₁   : ∀ {t i} → i ∈ᵤ P t → i ∈ᵤ P (suc t)
    -- The set Q is increasing over time.
    Qₜₛ⊆Q₁₊ₜₛ : ∀ {t s} (nf : Nonfull s) {i} → i ∈ᵤ Q t s → i ∈ᵤ Q (suc t) (s ∪ ⁅ next t s nf ⁆)


oneByOne-induction : (P : ℕ → Pred (Fin n) ℓ₁)
                     (Q : ℕ → Subset n → Pred (Fin n) ℓ₂) →
                     OneByOneInduction P Q →
                     ∀ i → P n i
oneByOne-induction {n} P Q hypotheses i =
  Ps n (subst (i ∈_) (sym (∣p∣≡n⇒p≡⊤ (t≤n⇒∣sₜ∣≡t ≤-refl))) ∈⊤)
  where
  open OneByOneInduction hypotheses

  mutual
    s : ℕ → Subset n
    s zero    = ⊥
    s (suc t) with t <? n
    ... | yes t<n = s t ∪ ⁅ next t (s t) (t<n⇒∣sₜ∣≢⊤ t<n) ⁆
    ... | no  t≮n = s t

    t≤n⇒∣sₜ∣≡t : ∀ {t} → t ≤ n → ∣ s t ∣ ≡ t
    t≤n⇒∣sₜ∣≡t {zero}  0≤n   = ∣⊥∣≡0 n
    t≤n⇒∣sₜ∣≡t {suc t} 1+t≤n with t <? n
    ... | no  t≮n = contradiction 1+t≤n t≮n
    ... | yes t<n = begin
      ∣ s t ∪ ⁅ next t (s t) _ ⁆ ∣ ≡⟨ ∣p∪⁅i⁆∣≡1+∣p∣ (next∉ t (s t) (t<n⇒∣sₜ∣≢⊤ t<n)) ⟩
      suc ∣ s t ∣                  ≡⟨ cong suc (t≤n⇒∣sₜ∣≡t (≤⇒pred≤ t<n)) ⟩
      suc t                        ∎ 
      where open ≡-Reasoning

    t<n⇒∣sₜ∣≢⊤ : ∀ {t} → t < n → Nonfull (s t)
    t<n⇒∣sₜ∣≢⊤ t<n = ∣p∣<n⇒Nonfull (subst (_< n) (sym (t≤n⇒∣sₜ∣≡t (<⇒≤ t<n))) t<n)

  t≥n⇒∣sₜ∣≡⊤ : ∀ {t} → n ≤ t → s t ≡ ⊤
  t≥n⇒∣sₜ∣≡⊤ {zero}  0≥n rewrite n≤0⇒n≡0 0≥n = refl
  t≥n⇒∣sₜ∣≡⊤ {suc t} n≤1+t with t <? n
  ... | no  t≮n = t≥n⇒∣sₜ∣≡⊤ (≮⇒≥ t≮n)
  ... | yes t<n = ∣p∣≡n⇒p≡⊤ (begin
    ∣ s t ∪ ⁅ next t (s t) _ ⁆ ∣ ≡⟨ ∣p∪⁅i⁆∣≡1+∣p∣ (next∉ t (s t) (t<n⇒∣sₜ∣≢⊤ t<n)) ⟩
    suc ∣ s t ∣                  ≡⟨ cong suc (t≤n⇒∣sₜ∣≡t (≤⇒pred≤ t<n)) ⟩
    suc t                        ≡⟨ ≤-antisym t<n n≤1+t ⟩
    n                            ∎)
    where open ≡-Reasoning

  mutual
    Ps : ∀ t → All (P t) (s t)
    Ps zero    i∈⊥    = contradiction i∈⊥ ∉⊥
    Ps (suc t) i∈s₁₊ₜ with t <? n
    ... | no  t≮n = Pₜ⊆Pₜ₊₁ (Ps t i∈s₁₊ₜ)
    ... | yes t<n with x∈p∪q⁻ _ _ i∈s₁₊ₜ
    ...   | inj₁ i∈sₜ     = Pₜ⊆Pₜ₊₁ (Ps t i∈sₜ)
    ...   | inj₂ i∈⁅next⁆ rewrite x∈⁅y⁆⇒x≡y _ i∈⁅next⁆ =
      P[next] t _ (t<n⇒∣sₜ∣≢⊤ t<n) (Ps t) (Q∁s t)

    Q∁s : ∀ t → All (Q t (s t)) (∁ (s t))
    Q∁s zero    {i} i∈∁s₀ = ∈Q₀⊥ _
    Q∁s (suc t) {i} i∈∁s₁₊ₜ with t <? n
    ... | no  t≮n = contradiction (subst (i ∈_) (trans (cong ∁ (t≥n⇒∣sₜ∣≡⊤ (≮⇒≥ t≮n))) ∁⊤≡⊥) i∈∁s₁₊ₜ) ∉⊥
    ... | yes t<n with x∉p∪q⁻ _ _ _ (x∈∁p⇒x∉p i∈∁s₁₊ₜ)
    ...   | (i∉sₜ , i∉⁅next⁆) = Qₜₛ⊆Q₁₊ₜₛ (t<n⇒∣sₜ∣≢⊤ t<n) (Q∁s t (x∉p⇒x∈∁p i∉sₜ))


record PositiveOneByOneInduction (P : ℕ → Pred (Fin n) ℓ₁) : Set ℓ₁ where
  field
    -- Given a subset, provides the next element to be added to it.
    next      : (t : ℕ) (s : Subset n) → Nonfull s → Fin n
    -- The next element is not in the subset
    next∉     : ∀ t s (nf : Nonfull s) → next t s nf ∉ s
    -- If all the elements within the subset satisfy P then the next element
    -- for that subset will also satisfy P
    P[next]   : ∀ t s (nf : Nonfull s) → All (P t) s → next t s nf ∈ᵤ P (suc t)
    -- The set P is increasing over time
    Pₜ⊆Pₜ₊₁   : ∀ {t i} → i ∈ᵤ P t → i ∈ᵤ P (suc t)


positiveOneByOne-induction : ∀ (P : ℕ → Pred (Fin n) ℓ₁) → PositiveOneByOneInduction P → ∀ i → P n i
positiveOneByOne-induction P rec = oneByOne-induction P (λ _ _ _ → ⊤ᵤ) (record
  { next      = next
  ; next∉     = next∉
  ; P[next]   = λ t s nf Ps _ → P[next] t s nf Ps
  ; ∈Q₀⊥      = _
  ; Pₜ⊆Pₜ₊₁   = Pₜ⊆Pₜ₊₁
  ; Qₜₛ⊆Q₁₊ₜₛ = _
  }) where open PositiveOneByOneInduction rec
