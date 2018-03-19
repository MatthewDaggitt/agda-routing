open import Data.Nat using (ℕ; suc; s≤s; z≤n;_+_; _≤_; _<_; _∸_; ≤-pred)
open import Data.Nat.Properties using (<⇒≤; ≤-refl; ≤-reflexive; <-irrefl; ≤-trans; n∸m≤n; n≤1+n; <⇒≱; m+n∸n≡m)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Nat.Properties using (∸-monoʳ-<; ∸-monoʳ-≤; m<n⇒0<n∸m; module ≤-Reasoning)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction as Step1ᶜ

module RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Step1_InconsistentHeightFunction
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  
  ------------------------------------------------------------------------------
  -- Inconsistent length
  ------------------------------------------------------------------------------
  -- The size of inconsistent routes where consistent routes are viewed as
  -- having the maximum size `n-1`

  private

    size≤n+1 : ∀ r → size r ≤ suc n
    size≤n+1 r = <⇒≤ (≤-trans (size<n _) (n≤1+n _))
    
    
  abstract
  
    hⁱ : Route → ℕ
    hⁱ r with 𝑪? r
    ... | yes _ = 1
    ... | no  _ = suc n ∸ size r
  
    Hⁱ : ℕ
    Hⁱ = suc n
  
    hⁱ-cong : ∀ {r s} → r ≈ s → hⁱ r ≡ hⁱ s
    hⁱ-cong {r} {s} r≈s with 𝑪? r | 𝑪? s
    ... | yes _  | yes _  = refl
    ... | no  rⁱ | yes sᶜ = contradiction (𝑪-cong (≈-sym r≈s) sᶜ) rⁱ
    ... | yes rᶜ | no  sⁱ = contradiction (𝑪-cong r≈s rᶜ) sⁱ
    ... | no  _  | no  _  = cong (suc n ∸_) (size-cong r≈s)
  
    hⁱ-decr : ∀ {i j x} → 𝑰 (A i j ▷ x) → hⁱ (A i j ▷ x) < hⁱ x
    hⁱ-decr {i} {j} {x} Aᵢⱼxⁱ with 𝑪? x | 𝑪? (A i j ▷ x)
    ... | yes xᶜ | _        = contradiction xᶜ (▷-forces-𝑰 Aᵢⱼxⁱ)
    ... | no  _  | yes Aᵢⱼxᶜ = contradiction Aᵢⱼxᶜ Aᵢⱼxⁱ
    ... | no  _  | no  _    = ∸-monoʳ-< (≤-reflexive (size-incr Aᵢⱼxⁱ)) (size≤n+1 _)

    h[sᶜ]<h[rⁱ] : ∀ {s r} → 𝑪 s → 𝑰 r → hⁱ s < hⁱ r
    h[sᶜ]<h[rⁱ] {s} {r} sᶜ rⁱ with 𝑪? s | 𝑪? r
    ... | no sⁱ | _      = contradiction sᶜ sⁱ
    ... | _     | yes rᶜ = contradiction rᶜ rⁱ
    ... | yes _ | no  _  = begin
      2                          ≡⟨ sym (m+n∸n≡m 2 n) ⟩
      suc (suc n) ∸ n            ≤⟨ ∸-monoʳ-≤ (size<n r) (suc (suc n)) ⟩
      suc (suc n) ∸ suc (size r) ≡⟨⟩ 
      suc n       ∸ size r       ∎
      where open ≤-Reasoning
    
    1≤hⁱ : ∀ r → 1 ≤ hⁱ r
    1≤hⁱ r with 𝑪? r
    ... | yes _ = s≤s z≤n
    ... | no  _ = m<n⇒0<n∸m (s≤s (<⇒≤ (size<n r)))
    
    hⁱ≤Hⁱ : ∀ r → hⁱ r ≤ Hⁱ
    hⁱ≤Hⁱ r with 𝑪? r
    ... | yes _ = s≤s z≤n
    ... | no  _ = n∸m≤n (size r) Hⁱ
