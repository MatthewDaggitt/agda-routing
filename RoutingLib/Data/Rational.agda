module RoutingLib.Data.Rational where

import Data.Integer as ℤ
open import Data.Integer.Properties using (≤-total)
open import Data.Rational
open import Relation.Nullary using (yes; no)

infix 4 _<_

data _<_ : ℚ → ℚ → Set where
  *<* : ∀ {p q} → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p) → p < q

infixl 7 _⊓_
_⊓_ : ℚ → ℚ → ℚ
p ⊓ q with (↥ p ℤ.* ↧ q) ℤ.≤? (↥ q ℤ.* ↧ q)
... | yes _ = p
... | no  _ = q

infixl 6 _⊔_
_⊔_ : ℚ → ℚ → ℚ
p ⊔ q with (↥ p ℤ.* ↧ q) ℤ.≤? (↥ q ℤ.* ↧ q)
... | yes _ = q
... | no  _ = p
