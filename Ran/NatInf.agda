-- imports
open import Data.Nat
  using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _⊓_ to _⊓ℕ_; _⊔_ to _⊔ℕ_)
open import Relation.Binary
  using (Rel; Decidable)
open import Level
  using () renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Relation.Nullary
  using (yes; no; ¬_)
open import Function
  using (_∘_)
open import Data.Sum
  using (_⊎_; [_,_])

module NatInf where

  data ℕ∞ : Set where
    ∞ : ℕ∞
    N : ℕ → ℕ∞

  infix 4 _≤_
  data _≤_ : Rel ℕ∞ lzero where
    z≤n : ∀ {n}                         → N zero  ≤ n
    s≤s : ∀ {m n} (m≤n : (N m) ≤ (N n)) → N (suc m) ≤ N (suc n)
    n≤∞ : ∀ {n}                         → n ≤ ∞

  data _≤'_ : Rel ℕ∞ lzero where
    ≤'-∞    : ∀ {m} → (N m) ≤' ∞
    ≤'-refl : ∀ {m}→ N m ≤' N m
    ≤'-step : ∀ {m n} (m≤'n : _≤'_ (N m) (N n)) → N m ≤' N (suc n)

  suc∞ : ℕ∞ → ℕ∞
  suc∞ ∞ = ∞
  suc∞ (N n) = N (suc n)

  _<'_ : Rel ℕ∞ lzero
  m <' n = suc∞ m ≤' n

  _≥_ : Rel ℕ∞ lzero
  n ≥ m = m ≤ n

  _≱_ : Rel ℕ∞ lzero
  m ≱ n = ¬ (m ≥ n)

  _≰_ : Rel ℕ∞ lzero
  m ≰ n = ¬ (m ≤ n)

  _<_ : Rel ℕ∞ lzero
  ∞ < n = ∞ ≤ n
  N m < n = N (suc m) ≤ n

  _>_ : Rel ℕ∞ lzero
  m > n = n < m

  _≮_ : Rel ℕ∞ lzero
  m ≮ n = ¬ (n < m)
  _+_ : ℕ∞ → ℕ∞ → ℕ∞
  ∞ + m = ∞
  N n + ∞ = ∞
  N n + N m = N (n +ℕ m)

  _⊓_ : ℕ∞ → ℕ∞ → ℕ∞
  ∞ ⊓ ∞ = ∞
  ∞ ⊓ N m = N m
  N n ⊓ ∞ = N n
  N n ⊓ N m = N (n ⊓ℕ m)

  _⊔_ : ℕ∞ → ℕ∞ → ℕ∞
  ∞ ⊔ m = ∞
  N n ⊔ ∞ = ∞
  N n ⊔ N m = N (n ⊔ℕ m)

  pred : ℕ∞ → ℕ∞
  pred ∞ = ∞
  pred (N zero) = N zero
  pred (N (suc n)) = N n

  _≟_ : Decidable {A = ℕ∞} _≡_
  ∞ ≟ ∞ = yes refl
  ∞ ≟ N n = no λ()
  N m ≟ ∞ = no λ()
  N zero ≟ N zero = yes refl
  N zero ≟ N (suc n) = no λ()
  N (suc m) ≟ N zero = no λ()
  N (suc m) ≟ N (suc n) with N m ≟ N n
  N (suc m) ≟ N (suc .m) | yes refl = yes refl
  N (suc m) ≟ N (suc n) | no ¬p = no (¬p ∘ (λ p → subst (λ x → (N m) ≡ pred x) p refl))

  ≤-pred : ∀ {m n} → N (suc m) ≤ N (suc n) → N m ≤ N n
  ≤-pred (s≤s m≤n) = m≤n

  _≤?_ : Decidable {A = ℕ∞} _≤_
  m ≤? ∞ = yes n≤∞
  ∞ ≤? N x = no λ ()
  N zero ≤? N x₁ = yes z≤n
  N (suc x) ≤? N zero = no λ ()
  N (suc x) ≤? N (suc x₁) with (N x) ≤? (N x₁)
  ... | yes p = yes (s≤s p)
  ... | no ¬p = no (¬p ∘ ≤-pred)

  extractℕ : ℕ∞ → ℕ
  extractℕ ∞ = 0
  extractℕ (N x) = x
