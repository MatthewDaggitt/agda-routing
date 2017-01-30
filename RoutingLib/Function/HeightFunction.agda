open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc; s≤s; decTotalOrder) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Rel; Poset; IsEquivalence; DecTotalOrder)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤ℕ-refl; antisym to ≤ℕ-antisym)

open import RoutingLib.Data.Nat.Properties using (m≤n∧m≢n⇨m<n)

module RoutingLib.Function.HeightFunction where

  record BoundedHeightFunction {a ℓ₁ ℓ₂} (poset : Poset a ℓ₁ ℓ₂) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    
    open Poset poset renaming (Carrier to A; refl to ≤-refl; antisym to ≤-antisym)
    open IsEquivalence isEquivalence using () renaming (refl to ≈-refl)

    field
      h : A → ℕ
      hₘₐₓ : ℕ
      h≤hₘₐₓ : ∀ {v} → h v ≤ℕ hₘₐₓ
      h-resp-≤ : ∀ {u v} → u ≤ v → h u ≤ℕ h v
      ≤-resp-h : ∀ {u v} → h u ≤ℕ h v → u ≤ v

      
    -- Some immediately derivable properties

    h-resp-≈ : ∀ {u v} → u ≈ v → h u ≡ h v
    h-resp-≈ u≈v = 
      ≤ℕ-antisym 
        (h-resp-≤ (proj₁ ≤-resp-≈ u≈v ≤-refl)) 
        (h-resp-≤ (proj₂ ≤-resp-≈ u≈v ≤-refl))

    ≈-resp-h : ∀ {u v} → h u ≡ h v → u ≈ v
    ≈-resp-h {u} h[u]≡h[v] =
      ≤-antisym 
        (≤-resp-h (subst (h u ≤ℕ_) h[u]≡h[v] ≤ℕ-refl)) 
        (≤-resp-h (subst (_≤ℕ h u) h[u]≡h[v] ≤ℕ-refl))

    h-resp-< : ∀ {u v} → u ≤ v × ¬ (u ≈ v) → h u <ℕ h v
    h-resp-< {u} {v} (u≤v , u≉v) = m≤n∧m≢n⇨m<n (h-resp-≤ u≤v) (λ hu≡hv → u≉v (≈-resp-h hu≡hv))
