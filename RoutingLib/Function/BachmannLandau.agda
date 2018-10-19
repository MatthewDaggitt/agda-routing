open import Data.Nat
open import Data.Product
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary
open import Relation.Unary using (_∈_)

open import RoutingLib.Data.Nat.Properties

module RoutingLib.Function.BachmannLandau where

-----------------
-- Definitions --
-----------------

Ω[_] : Rel (ℕ → ℕ) 0ℓ
Ω[ g ] f = ∃₂ λ c k → ∀ {n} → k ≤ n → c * g n ≤ f n

Θ[_] : Rel (ℕ → ℕ) 0ℓ
Θ[ g ] f = ∃₂ λ c d → ∃ λ k → ∀ {n} → k ≤ n → c * g n ≤ f n × f n ≤ d * g n

O[_] : Rel (ℕ → ℕ) 0ℓ
O[ g ] f = ∃₂ λ c k → ∀ {n} → k ≤ n → f n ≤ c * g n

----------------
-- Properties --
----------------

{-
Ω-linear : ∀ {f g a b} → 0 < a → f ∈ Ω[ (λ n → a * (g n) + b) ] → f ∈ Ω[ g ]
Ω-linear 0<a (c , k , ag+c≤f) = c , k , λ k≤n → {!≤-trans ? ?!}
-}

Ω+O⇒Θ : ∀ {f g} → f ∈ Ω[ g ] → f ∈ O[ g ] → f ∈ Θ[ g ]
Ω+O⇒Θ (c , k₁ , leq) (d , k₂ , geq) =
  c , d , k₁ ⊔ k₂ , λ k₁⊔k₂≤n → leq (m⊔n≤o⇒m≤o k₁⊔k₂≤n) , geq (m⊔n≤o⇒n≤o k₁⊔k₂≤n)
