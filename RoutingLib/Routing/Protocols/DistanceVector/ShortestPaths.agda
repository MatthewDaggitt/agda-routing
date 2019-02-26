
module RoutingLib.Routing.Protocols.DistanceVector.ShortestPaths where

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; cong)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties

open import RoutingLib.Routing.Algebra

Aˢʰᵒʳᵗᵉˢᵗ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aˢʰᵒʳᵗᵉˢᵗ = record
  { Route              = ℕ∞
  ; Step               = λ _ _ → ℕ∞
  ; _≈_                = _≡_
  ; _⊕_                = _⊓_
  ; _▷_                = _+_
  ; 0#                 = N 0
  ; ∞#                 = ∞
  ; f∞                 = λ _ _ → ∞
  ; ≈-isDecEquivalence = ≡-isDecEquivalence
  ; ⊕-cong             = cong₂ _⊓_
  ; ▷-cong             = λ f → cong (f +_)
  ; f∞-reject          = λ _ _ _ → refl
  }

isRoutingAlgebra : IsRoutingAlgebra Aˢʰᵒʳᵗᵉˢᵗ
isRoutingAlgebra = record
  { ⊕-sel        = ⊓-sel
  ; ⊕-comm       = ⊓-comm
  ; ⊕-assoc      = ⊓-assoc
  ; ⊕-zeroʳ       = ⊓-zeroʳ
  ; ⊕-identityʳ   = ⊓-identityʳ
  ; ▷-fixedPoint = +-zeroʳ
  }

isDistributive : IsDistributive Aˢʰᵒʳᵗᵉˢᵗ
isDistributive = +-distribˡ-⊓
