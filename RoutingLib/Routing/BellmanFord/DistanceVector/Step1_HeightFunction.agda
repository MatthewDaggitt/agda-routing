open import Data.Nat using (ℕ; suc; z≤n; s≤s; _∸_) renaming (_≤_ to _≤ℕ_; _≥_ to _≥ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<⇒≤; n∸m≤n) renaming (≤-reflexive to ≤ℕ-reflexive; ≤-trans to ≤ℕ-trans; ≤-antisym to ≤ℕ-antisym; ≤-decTotalOrder to ≤ℕ-decTotalOrder)
open import Data.List using (List; length)
open import Data.Product using (∃; _,_)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.List using (index; between)
open import RoutingLib.Data.List.Uniqueness using (Unique)
open import RoutingLib.Data.List.Uniqueness.Properties using (between!⁺)
open import RoutingLib.Data.List.Sorting.Nat using (↗-between)
open import RoutingLib.Data.List.Any.Membership.Properties using (indexOf-cong; indexOf-revCong; indexOf-index; indexOf[xs]≤|xs|; indexOf[xs]<|xs|)
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-between⁺; ∈-between⁻)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; ∸-cancelˡ-≡; ∸-monoˡ-<; ∸-cancelˡ-≤; m<n⇒0<n∸m; n∸1+m<n; m∸[m∸n]≡n)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using (SufficientConditions)
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude

module RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction 
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where
  
  open Prelude 𝓡𝓟 𝓢𝓒

  open import Data.List.Any.Membership ℕₛ using () renaming (_∈_ to _∈ℕ_)

  open import RoutingLib.Data.List.Any.Membership S using (indexOf)
  
  open import RoutingLib.Data.List.Sorting ≤ℕ-decTotalOrder using () renaming (Sorted to Sortedℕ)
  open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder using (↗-unique; ↗-∈ˡ; ↗-indexOf-mono-<; ↗-indexOf-revMono-≤; ↗-indexOf-⊤)


  abstract
  
    -- The height of an element x is h(x) = H ∸ |{y | y ≤ x}|

    
    h : Route → ℕ
    h x = H ∸ indexOf (∈-↗routes x)

    h-resp-≈ : ∀ {u v} → u ≈ v → h u ≡ h v
    h-resp-≈ {u} {v} u≈v = cong (H ∸_) (indexOf-cong S u≈v (∈-↗routes u) (∈-↗routes v) ↗routes!)

    ≈-resp-h : ∀ {u v} → h u ≡ h v → u ≈ v
    ≈-resp-h {u} {v} hᵤ≡hᵥ = indexOf-revCong S (∈-↗routes u) (∈-↗routes v) (∸-cancelˡ-≡ (indexOf[xs]≤|xs| S _) (indexOf[xs]≤|xs| S _) hᵤ≡hᵥ)

    h-resp-< : ∀ {u v} → u < v → h v <ℕ h u
    h-resp-< {u} {v} u<v = ∸-monoˡ-< (↗-indexOf-mono-< ↗-↗routes (∈-↗routes u) (∈-↗routes v) u<v) (indexOf[xs]≤|xs| S _)

    h-resp-≤ : h Preserves _≤_ ⟶ _≥ℕ_
    h-resp-≤ {u} {v} u≤v with u ≟ v
    ... | yes u≈v = ≤ℕ-reflexive (h-resp-≈ (≈-sym u≈v))
    ... | no  u≉v = <⇒≤ (h-resp-< (u≤v , u≉v))

    postulate h-resp-≤₂ : h Preserves _≤_ ⟶ _≤ℕ_
    
    ≤-resp-h : ∀ {u v} → h u ≤ℕ h v → v ≤ u
    ≤-resp-h {u} {v} h[u]≤h[v] = ↗-indexOf-revMono-≤ ↗-↗routes (∈-↗routes v) (∈-↗routes u) (∸-cancelˡ-≤ (indexOf[xs]≤|xs| S _) h[u]≤h[v])


    1≤h : ∀ x → 1 ≤ℕ h x
    1≤h x = m<n⇒0<n∸m (indexOf[xs]<|xs| S (∈-↗routes x)) --s≤s z≤n

    h≤H : ∀ x → h x ≤ℕ H
    h≤H x = n∸m≤n (indexOf (∈-↗routes x)) H

    1≤H : 1 ≤ℕ H
    1≤H = ≤ℕ-trans (1≤h 0#) (h≤H 0#)

    postulate h0≡1 : h 0# ≡ 1
    
    h-incr : ∀ e {x} → x ≉ 0# → h (e ▷ x) <ℕ h x
    h-incr e x≉0 = h-resp-< (⊕-almost-strictly-absorbs-▷ e x≉0)



{-
    -- Furthermore for any valid height, we can retrieve the route with that height

    h⁻¹ : ∀ {i} → 1 ≤ℕ i → i ≤ℕ H → Route
    h⁻¹ {suc i} (s≤s z≤n) i≤H = index ↗routes (n∸1+m<n i 1≤H)
    
    h⁻¹-isInverse : ∀ {i} (1≤i : 1 ≤ℕ i) i≤H → h (h⁻¹ 1≤i i≤H) ≡ i
    h⁻¹-isInverse {suc i} (s≤s z≤n) i<H = begin
      h (h⁻¹ (s≤s z≤n) i<H) ≡⟨ cong (H ∸_) (indexOf-index S ↗routes! (n∸1+m<n i 1≤H) (∈-↗routes _)) ⟩
      H ∸ (H ∸ (suc i))     ≡⟨ m∸[m∸n]≡n i<H ⟩
      suc i                 ∎
      where open ≡-Reasoning


    -- We can therefore reconstruct the image of the h

    h-image : List ℕ
    h-image = between 1 (suc H)

    h-image! : Unique ℕₛ h-image
    h-image! = between!⁺ 1 (suc H)

    h-image-complete : ∀ x → h x ∈ℕ h-image
    h-image-complete x = ∈-between⁺ (1≤h x) (s≤s (h≤H x))

    h-image-sound : ∀ {i} → i ∈ℕ h-image → ∃ λ x → h x ≡ i
    h-image-sound {i} i∈betw with ∈-between⁻ 1 (suc H) i∈betw
    ... | 1≤i , (s≤s i≤H) = h⁻¹ 1≤i i≤H , h⁻¹-isInverse 1≤i i≤H

    h-image↗ : Sortedℕ h-image
    h-image↗ = ↗-between 1 (suc H)
-}
