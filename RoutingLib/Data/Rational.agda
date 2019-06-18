

module RoutingLib.Data.Rational where


open import Data.Nat using (ℕ)
open import Data.Integer as ℤ using (+_)
open import Data.Integer.Properties using (≤-total)
open import Data.Rational
open import Relation.Nullary using (yes; no)

infixl 7 _⊓_
_⊓_ : ℚ → ℚ → ℚ
p ⊓ q with (↥ p ℤ.* ↧ q) ℤ.≤? (↥ q ℤ.* ↧ p)
... | yes _ = p
... | no  _ = q

infixl 6 _⊔_
_⊔_ : ℚ → ℚ → ℚ
p ⊔ q with (↥ p ℤ.* ↧ q) ℤ.≤? (↥ q ℤ.* ↧ p)
... | yes _ = q
... | no  _ = p

fromℕ : ℕ → ℚ
fromℕ n = + n / 1
