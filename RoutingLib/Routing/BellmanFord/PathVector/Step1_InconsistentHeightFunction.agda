open import Data.Nat using (ℕ; suc; s≤s; z≤n;_+_; _≤_; _<_; _∸_; ≤-pred)
open import Data.Nat.Properties using (<⇒≤; ≤-refl; ≤-reflexive; <-irrefl; ≤-trans; n∸m≤n)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Graph.SimplePath using (SimplePath; length)
open import RoutingLib.Data.Nat.Properties using (∸-monoʳ-<)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction as Step1ᶜ

module RoutingLib.Routing.BellmanFord.PathVector.Step1_InconsistentHeightFunction
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  --open import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction 𝓡𝓟ᶜ 𝓢𝓒 using () renaming (hₘₐₓ to Hᶜ)
  
  ------------------------------------------------------------------------------
  -- Inconsistent length
  ------------------------------------------------------------------------------
  -- The size of inconsistent routes where consistent routes are viewed as
  -- having the maximum size `n-1`

  abstract
  
    hⁱ : Route → ℕ
    hⁱ r with 𝑪? r
    ... | yes _ = 1
    ... | no  _ = n ∸ size r
  
    Hⁱ : ℕ
    Hⁱ = n
  
    hⁱ-cong : ∀ {r s} → r ≈ s → hⁱ r ≡ hⁱ s
    hⁱ-cong {r} {s} r≈s with 𝑪? r | 𝑪? s
    ... | yes _  | yes _  = refl
    ... | no  rⁱ | yes sᶜ = contradiction (𝑪-cong (≈-sym r≈s) sᶜ) rⁱ
    ... | yes rᶜ | no  sⁱ = contradiction (𝑪-cong r≈s rᶜ) sⁱ
    ... | no  _  | no  _  = cong (n ∸_) (size-cong r≈s)
  
    
    
    hⁱ-decr : ∀ f {x} → 𝑰 x → hⁱ (f ▷ x) < hⁱ x
    hⁱ-decr f {x} xⁱ with 𝑪? x | 𝑪? (f ▷ x)
    ... | yes xᶜ | _     = contradiction xᶜ xⁱ
    ... | no  _  | yes _ = {!!}
    ... | no  _  | no  _ = ∸-monoʳ-< {m = n} {n = size (f ▷ x)} {o = size x} {!!} (<⇒≤ (size<n (f ▷ x)))
    
    postulate h[s]≤h[rᶜ] : ∀ s {r} → 𝑪 r → hⁱ s ≤ hⁱ r → 𝑪 s

    1≤hⁱ : ∀ r → 1 ≤ hⁱ r
    1≤hⁱ = {!!}
    
    hⁱ≤Hⁱ : ∀ r → hⁱ r ≤ Hⁱ
    hⁱ≤Hⁱ r with 𝑪? r
    ... | yes _ = s≤s z≤n
    ... | no  _ = n∸m≤n (size r) n


