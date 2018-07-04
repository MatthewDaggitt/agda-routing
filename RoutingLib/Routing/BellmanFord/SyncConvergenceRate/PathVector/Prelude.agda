open import Data.Nat using (ℕ; suc; z≤n; s≤s; _<_)
open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong; module ≡-Reasoning)

open import RoutingLib.Data.SimplePath renaming (_∈_ to _∈ₚ_)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.Properties using (length-cong)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra as IncreasingPathAlgebraProperties
import RoutingLib.Routing.BellmanFord as BellmanFord
import RoutingLib.Routing.BellmanFord.Properties as BellmanFordProperties
import RoutingLib.Routing.BellmanFord.PathProperties as BellmanFordPathProperties

module RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Prelude
  {a b ℓ n-1} (algebra : IncreasingPathAlgebra a b ℓ (suc n-1))
  where
  
  open IncreasingPathAlgebra algebra public
  open IncreasingPathAlgebraProperties algebra public
  
  open BellmanFord rawRoutingAlgebra A public
  open BellmanFordProperties routingAlgebra A public
  open BellmanFordPathProperties pathAlgebra public

  n : ℕ
  n = suc n-1
  
  𝕋 : Set
  𝕋 = ℕ


  module Notation (X : RMatrix) (j : Fin n) where

    --------------------------------------------------------------------------
    -- Some notation for comparing edges.

    weightₑ : 𝕋 → Edge → Route
    weightₑ t (i , k) = A i k ▷ σ^ t X k j

    --------------------------------------------------------------------------
    -- Some notation for comparing edges.

    _≤[_]_ : Edge → 𝕋 → Edge → Set _
    e₁ ≤[ t ]  e₂ = weightₑ t e₁ ≤₊  weightₑ t e₂

    _≤[_]?_ : ∀ e t f → Dec (e ≤[ t ] f)
    e₁ ≤[ t ]? e₂ = weightₑ t e₁ ≤₊? weightₑ t e₂

    _<[_]_ : Edge → 𝕋 → Edge → Set _
    e₁ <[ t ]  e₂ = weightₑ t e₁ <₊  weightₑ t e₂

    _<[_]?_ : ∀ e t f → Dec (e <[ t ] f)
    e₁ <[ t ]? e₂ = weightₑ t e₁ <₊? weightₑ t e₂

    --------------------------------------------------------------------------
    -- The length of the route used by edge i at time t + s

    lengthₑ : 𝕋 → Edge → ℕ
    lengthₑ t (i , k) = size (σ^ t X k j)

    lengthₑ<n : ∀ s e → lengthₑ s e < n
    lengthₑ<n t (i , k) = size<n (s≤s z≤n) (σ^ t X k j)

    lengthₑ-extension : ∀ i {t k l e p ∼₁ ∼₂} →
                        path (σ^ (suc t) X k j) ≈ₚ valid (e ∷ p ∣ ∼₁ ∣ ∼₂) →
                        path (σ^ t X l j) ≈ₚ valid p →
                        lengthₑ (suc t) (i , k) ≡ suc (lengthₑ t (k , l))
    lengthₑ-extension i {t} {k} {l} {e} {p} p[σᵗ⁺¹⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p = begin
      lengthₑ (suc t) (i , k)          ≡⟨⟩
      length (path (σ^ (suc t) X k j)) ≡⟨ length-cong p[σᵗ⁺¹⁺ˢ]≈kl∷p ⟩
      suc (length (valid p))           ≡⟨ sym (cong suc (length-cong p[σᵗ⁺ˢXₗⱼ]≈p)) ⟩
      suc (length (path (σ^ t X l j))) ≡⟨⟩
      suc (lengthₑ t (k , l))          ∎
      where open ≡-Reasoning


    lengthₙ : 𝕋 → Node → ℕ
    lengthₙ t k = size (σ^ t X k j)

    lengthₙ<n : ∀ s e → lengthₙ s e < n
    lengthₙ<n t k = size<n (s≤s z≤n) (σ^ t X k j)

    lengthₙ-extension : ∀ {t k l e p ∼₁ ∼₂} →
                        path (σ^ (suc t) X k j) ≈ₚ valid (e ∷ p ∣ ∼₁ ∣ ∼₂) →
                        path (σ^ t X l j) ≈ₚ valid p →
                        lengthₙ (suc t) k ≡ suc (lengthₙ t l)
    lengthₙ-extension {t} {k} {l} {e} {p} p[σᵗ⁺¹⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p = begin
      lengthₙ (suc t) k                ≡⟨⟩
      length (path (σ^ (suc t) X k j)) ≡⟨ length-cong p[σᵗ⁺¹⁺ˢ]≈kl∷p ⟩
      suc (length (valid p))           ≡⟨ sym (cong suc (length-cong p[σᵗ⁺ˢXₗⱼ]≈p)) ⟩
      suc (length (path (σ^ t X l j))) ≡⟨⟩
      suc (lengthₙ t l)                ∎
      where open ≡-Reasoning
