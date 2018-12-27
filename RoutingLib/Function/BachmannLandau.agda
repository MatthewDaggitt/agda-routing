open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Function using (_∘_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (sym)

open import RoutingLib.Data.Nat.Properties hiding (module ≤-Reasoning)
open ≤-Reasoning

module RoutingLib.Function.BachmannLandau where

-----------------
-- Definitions --
-----------------

Ω[_] : Rel (ℕ → ℕ) 0ℓ
Ω[ g ] f = ∃₂ λ c k → ∀ {n} → k ≤ n → suc c * g n ≤ f n

Θ[_] : Rel (ℕ → ℕ) 0ℓ
Θ[ g ] f = ∃₂ λ c d → ∃ λ k → ∀ {n} → k ≤ n → suc c * g n ≤ f n × f n ≤ d * g n

O[_] : Rel (ℕ → ℕ) 0ℓ
O[ g ] f = ∃₂ λ c k → ∀ {n} → k ≤ n → f n ≤ c * g n

open import Relation.Unary public using (_∈_)

----------------
-- Properties --
----------------

Ω-linear⁺ : ∀ {f g a b} → 0 < a → f ∈ Ω[ (λ n → a * (g n) + b) ] → f ∈ Ω[ g ]
Ω-linear⁺ {f} {g} {a} {b} 0<a (c , k , ag+c≤f) = c , k , λ {n} k≤n → begin
  suc c * g n                     ≤⟨ *-monoʳ-≤ (suc c) (a≤b*a 0<a) ⟩
  suc c * (a * g n)               ≤⟨ m≤m+n _ _ ⟩
  suc c * (a * g n) + (suc c) * b ≡⟨ sym (*-distribˡ-+ (suc c) (a * g n) b) ⟩
  suc c * (a * g n + b)           ≤⟨ ag+c≤f k≤n ⟩
  f n                             ∎

Ω-linear⁻ : ∀ {f g a b} → 0 < a → f ∈ Ω[ g ] → f ∈ Ω[ (λ n → a * (g n) + b) ]
Ω-linear⁻ {f} {g} {a} {b} 0<a (c , k , g≤f) = {!!} , k , λ {n} k≤n → begin
  (suc {!!}) * (a * g n + b) ≤⟨ {!!} ⟩
  (suc c) * g n              ≤⟨ g≤f k≤n ⟩
  f n                        ∎

Ω+O⇒Θ : ∀ {f g} → f ∈ Ω[ g ] → f ∈ O[ g ] → f ∈ Θ[ g ]
Ω+O⇒Θ (c , k₁ , leq) (d , k₂ , geq) =
  c , d , k₁ ⊔ k₂ , < leq ∘ m⊔n≤o⇒m≤o , geq ∘ m⊔n≤o⇒n≤o >
