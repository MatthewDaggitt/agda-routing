
open import Data.Nat using (ℕ; suc; z≤n; s≤s; _<_)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Prelude
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  where

open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong; module ≡-Reasoning)

import RoutingLib.Routing.Basics.Path.CertifiedI as CertifiedPaths
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties using (length-cong)

import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties
import RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra as CertifiedPathAlgebraProperties
import RoutingLib.Routing.VectorBased.Synchronous as BellmanFord
import RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties as BellmanFordProperties
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Properties as BellmanFordPathProperties

open RawRoutingAlgebra algebra public
open IsRoutingAlgebra isRoutingAlgebra public
open IsCertifiedPathAlgebra isPathAlgebra public
open RoutingAlgebraProperties isRoutingAlgebra public
open CertifiedPathAlgebraProperties isRoutingAlgebra isPathAlgebra public

open CertifiedPaths public hiding (Edge; Vertex)

open BellmanFord algebra A public
open BellmanFordProperties isRoutingAlgebra A public
open BellmanFordPathProperties isRoutingAlgebra isPathAlgebra A public

n : ℕ
n = suc n-1

𝕋 : Set
𝕋 = ℕ

Edge : Set
Edge = CertifiedPaths.Edge n

module Notation (X : RoutingMatrix) (j : Node) where

  --------------------------------------------------------------------------
  -- Some notation for comparing edges.

  weightₑ : 𝕋 → Edge → PathWeight
  weightₑ t (i , k) = A i k ▷ σ t X k j

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
  lengthₑ t (i , k) = size (σ t X k j)

  lengthₑ<n : ∀ s e → lengthₑ s e < n
  lengthₑ<n t (i , k) = size<n (s≤s z≤n) (σ t X k j)

  lengthₑ-extension : ∀ i {t k l e p ∼₁ ∼₂} →
                      path (σ (suc t) X k j) ≈ₚ valid (e ∷ p ∣ ∼₁ ∣ ∼₂) →
                      path (σ t X l j) ≈ₚ valid p →
                      lengthₑ (suc t) (i , k) ≡ suc (lengthₑ t (k , l))
  lengthₑ-extension i {t} {k} {l} {e} {p} p[σᵗ⁺¹⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p = begin
    lengthₑ (suc t) (i , k)          ≡⟨⟩
    length (path (σ (suc t) X k j)) ≡⟨ length-cong p[σᵗ⁺¹⁺ˢ]≈kl∷p ⟩
    suc (length (valid p))           ≡⟨ sym (cong suc (length-cong p[σᵗ⁺ˢXₗⱼ]≈p)) ⟩
    suc (length (path (σ t X l j))) ≡⟨⟩
    suc (lengthₑ t (k , l))          ∎
    where open ≡-Reasoning


  lengthₙ : 𝕋 → Node → ℕ
  lengthₙ t k = size (σ t X k j)

  lengthₙ<n : ∀ s e → lengthₙ s e < n
  lengthₙ<n t k = size<n (s≤s z≤n) (σ t X k j)

  lengthₙ-extension : ∀ {t k l e p ∼₁ ∼₂} →
                      path (σ (suc t) X k j) ≈ₚ valid (e ∷ p ∣ ∼₁ ∣ ∼₂) →
                      path (σ t X l j) ≈ₚ valid p →
                      lengthₙ (suc t) k ≡ suc (lengthₙ t l)
  lengthₙ-extension {t} {k} {l} {e} {p} p[σᵗ⁺¹⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p = begin
    lengthₙ (suc t) k                ≡⟨⟩
    length (path (σ (suc t) X k j))  ≡⟨ length-cong p[σᵗ⁺¹⁺ˢ]≈kl∷p ⟩
    suc (length (valid p))           ≡⟨ sym (cong suc (length-cong p[σᵗ⁺ˢXₗⱼ]≈p)) ⟩
    suc (length (path (σ t X l j)))  ≡⟨⟩
    suc (lengthₙ t l)                ∎
    where open ≡-Reasoning

