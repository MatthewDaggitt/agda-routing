open import Data.Nat as ℕ using (ℕ; suc; _∸_)
-- open import Data.Nat.Properties
open import Data.Product
open import Data.Rational
open import Data.Rational.Properties
open import Function using (_∘_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (sym; _≗_)

open import Data.Rational
open import Data.Rational.Properties
open import RoutingLib.Data.Nat.Properties using (a≤b*a)
-- open ≤-Reasoning

module RoutingLib.Function.BachmannLandau where

--------------------------------------------------------------------------------
-- Definitions

open import Relation.Unary public using (_∈_)

O[_] : Rel (ℚ → ℚ) 0ℓ
O[ g ] f = ∃₂ λ c k → ∀ {n} → k ≤ n → f n ≤ c * g n

Ω[_] : Rel (ℚ → ℚ) 0ℓ
Ω[ g ] f = ∃₂ λ c k → 0ℚ < c → ∀ {n} → k ≤ n → c * g n ≤ f n

Θ[_] : Rel (ℚ → ℚ) 0ℓ
Θ[ g ] f = ∃₂ λ c d → 0ℚ < c → ∃ λ k → ∀ {n} → k ≤ n → c * g n ≤ f n × f n ≤ d * g n

--------------------------------------------------------------------------------
-- Properties of O

O-refl : ∀ {f} → f ∈ O[ f ]
O-refl = 1ℚ , 0ℚ , λ 0≤n → ≤-reflexive (sym (*-identityˡ _))

O-trans : ∀ {f g h} → f ∈ O[ g ] → g ∈ O[ h ] → f ∈ O[ h ]
O-trans {f} {g} {h} (c , k , cg≤f) (d , l , dh≤g) = c * d , k ⊔ l , λ {n} k⊔l≤n →
  {!!}

{-
O-scaling⁺ : ∀ {f g a} → f ∈ O[ (λ n → a * g n) ] → f ∈ O[ g ]
O-scaling⁺ {f} {g} {a} (c , k , f≤cag) = c * a , k , λ {n} k≤n → begin
  f n             ≤⟨ f≤cag k≤n ⟩
  c * (a * g n)   ≡⟨ sym (*-assoc c a (g n))  ⟩
  (c * a) * g n   ∎

O-scaling⁻ : ∀ {f g a} → f ∈ O[ g ] → f ∈ O[ (λ n → suc a * g n) ]
O-scaling⁻ {f} {g} {a} (c , k , f≤cg) = c , k , λ {n} k≤n → begin
  f n               ≤⟨ f≤cg k≤n ⟩
  c * g n           ≤⟨ *-monoʳ-≤ c (a≤b*a (g n) a)  ⟩
  c * (suc a * g n) ∎

--------------------------------------------------------------------------------
-- Properties of Ω

Ω-refl : ∀ {f} → f ∈ Ω[ f ]
Ω-refl = 0 , 0 , λ _ → ≤-reflexive (+-identityʳ _)

Ω-trans : ∀ {f g h} → f ∈ Ω[ g ] → g ∈ Ω[ h ] → f ∈ Ω[ h ]
Ω-trans {f} {g} {h} (c-1 , k , cg≤f) (d-1 , l , dh≤g) =
  (c * d) ∸ 1 , k ⊔ l , λ {n} k⊔l≤n → begin
  suc (c * d ∸ 1) * h n ≡⟨⟩
  c * d       * h n     ≡⟨ *-assoc c d (h n) ⟩
  c * (d * h n)         ≤⟨ *-monoʳ-≤ c (dh≤g (m⊔n≤o⇒n≤o k l k⊔l≤n)) ⟩
  c * g n               ≤⟨ cg≤f (m⊔n≤o⇒m≤o k l k⊔l≤n) ⟩
  f n                   ∎
  where c = suc c-1; d = suc d-1

Ω-linear : ∀ {f g a b} → f ∈ Ω[ (λ n → suc a * (g n) + b) ] → f ∈ Ω[ g ]
Ω-linear {f} {g} {a-1} {b} (c-1 , k , ag+c≤f) = c-1 , k , λ {n} k≤n → begin
  c * g n               ≤⟨ *-monoʳ-≤ c (a≤b*a (g n) a-1) ⟩
  c * (a * g n)         ≤⟨ m≤m+n _ _ ⟩
  c * (a * g n) + c * b ≡⟨ sym (*-distribˡ-+ c (a * g n) b) ⟩
  c * (a * g n + b)     ≤⟨ ag+c≤f k≤n ⟩
  f n                   ∎
  where a = suc a-1; c = suc c-1

--------------------------------------------------------------------------------
-- Properties of Θ

Θ⇒O : ∀ {f g} → f ∈ Θ[ g ] → f ∈ O[ g ]
Θ⇒O (c-1 , d , k , cg≤f≤dg) = d , k , proj₂ ∘ cg≤f≤dg

Θ⇒Ω : ∀ {f g} → f ∈ Θ[ g ] → f ∈ Ω[ g ]
Θ⇒Ω (c-1 , d , k , cg≤f≤dg) = c-1 , k , proj₁ ∘ cg≤f≤dg

O+Ω⇒Θ : ∀ {f g} → f ∈ O[ g ] → f ∈ Ω[ g ] → f ∈ Θ[ g ]
O+Ω⇒Θ (d , k₂ , geq) (c , k₁ , leq) =
  c , d , k₁ ⊔ k₂ , < leq ∘ m⊔n≤o⇒m≤o k₁ k₂ , geq ∘ m⊔n≤o⇒n≤o k₁ k₂ >

θ-refl : ∀ {f} → f ∈ Θ[ f ]
θ-refl = O+Ω⇒Θ O-refl Ω-refl

Θ-trans : ∀ {f g h} → f ∈ Θ[ g ] → g ∈ Θ[ h ] → f ∈ Θ[ h ]
Θ-trans f∈Θ[g] g∈Θ[h] = O+Ω⇒Θ
  (O-trans (Θ⇒O f∈Θ[g]) (Θ⇒O g∈Θ[h]))
  (Ω-trans (Θ⇒Ω f∈Θ[g]) (Θ⇒Ω g∈Θ[h]))
-}
