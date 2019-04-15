

module RoutingLib.Data.Rational.Properties where

open import Data.Rational

open import RoutingLib.Data.Rational

postulate p⊔q≤p+q : ∀ p q → p ⊔ q ≤ p + q
