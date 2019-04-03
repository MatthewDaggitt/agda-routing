

module RoutingLib.Data.Rational where

import Data.Integer as ℤ
open import Data.Integer.Properties using (≤-total)
open import Data.Rational
open import Data.Sum using (inj₁; inj₂)

infix 4 _<_

data _<_ : ℚ → ℚ → Set where
  *<* : ∀ {p q} → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p) → p < q

infixl 7 _⊓_
_⊓_ : ℚ → ℚ → ℚ
p ⊓ q with ≤-total (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ q)
... | inj₁ _ = p
... | inj₂ _ = q

infixl 6 _⊔_
_⊔_ : ℚ → ℚ → ℚ
p ⊔ q with ≤-total (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ q)
... | inj₁ _ = q
... | inj₂ _ = p
