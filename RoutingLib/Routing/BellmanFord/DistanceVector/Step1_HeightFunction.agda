open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions

module RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction 
  {a b ℓ n}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 n) 
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where

  open import Data.Nat using (ℕ; suc; z≤n; s≤s; _≤_; _<_)
  open import Data.Fin using (toℕ) renaming (_<_ to _<𝔽_)
  open import Data.Fin.Properties using (prop-toℕ-≤)
  open import Data.List using (List; length)
  open import Data.List.Any using (index)
  open import Data.Product using (_,_; _×_; map)
  open import Relation.Binary using (_Preserves_⟶_)
  open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; setoid)
  open import Function using (_∘_; id; _$_)
  
  open import Data.List.Any.Membership (setoid ℕ) using () renaming (_∈_ to _∈ℕ_)

  open import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude 𝓡𝓟 𝓢𝓒

  open import RoutingLib.Data.Fin.Properties using (toℕ-mono-<)
  open import RoutingLib.Data.List.Membership.Setoid.Properties using (index-cong)
  open import RoutingLib.Data.Nat.Properties using (ℕₛ; suc∘pred[n]≡n)
  open import RoutingLib.Data.List.Membership.Setoid S using ()
  open import RoutingLib.Data.List.Sorting.Properties ≥₊-decTotalOrder using (index-mono-<)

  open import RoutingLib.Function.Reasoning
  
  abstract
    
    -- The height of an element x is h(x) = |{y | x ≤ y}|

    h : Route → ℕ
    h x = suc (toℕ (index (∈-routes x)))
    
    h-cong : h Preserves _≈_ ⟶ _≡_
    h-cong {u} {v} u≈v = u≈v
      ∶ u ≈ v                                   ∣>′ index-cong S (∈-routes u) (∈-routes v) routes!
      ∶ index (∈-routes u) ≡ index (∈-routes v) ∣>′ cong (suc ∘ toℕ)
      ∶ h u ≡ h v

    h-resp-< : ∀ {u v} → u <₊ v → h v < h u
    h-resp-< {u} {v} u<v = u<v
      ∶ u ≤₊ v × u ≉ v                           ∣>′ map id (λ u≉v → u≉v ∘ ≈-sym)
      ∶ u ≤₊ v × v ≉ u                           ∣>′ index-mono-< routes↗ (∈-routes _) (∈-routes _)
      ∶ index (∈-routes v) <𝔽 index (∈-routes u) ∣>′ s≤s ∘ toℕ-mono-<
      ∶ h v < h u
      
    1≤h : ∀ x → 1 ≤ h x
    1≤h _ = s≤s z≤n

    h≤H : ∀ x → h x ≤ H
    h≤H x = subst (h x ≤_) (suc∘pred[n]≡n 1≤H) (s≤s (prop-toℕ-≤ (index (∈-routes x))))
      
    
