
module RoutingLib.Routing.Protocols.DistanceVector.WidestPaths where

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; cong)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties

open import RoutingLib.Routing.Algebra

Aʷⁱᵈᵉˢᵗ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aʷⁱᵈᵉˢᵗ = record
  { Route              = ℕ∞
  ; Step               = λ _ _ → ℕ∞
  ; _≈_                = _≡_
  ; _⊕_                = _⊔_
  ; _▷_                = _⊓_
  ; 0#                 = ∞
  ; ∞#                 = N 0
  ; f∞                 = λ _ _ → N 0
  ; ≈-isDecEquivalence = ≡-isDecEquivalence
  ; ⊕-cong             = cong₂ _⊔_
  ; ▷-cong             = λ f → cong (f ⊓_)
  ; f∞-reject          = λ _ _ _ → ⊓-zeroˡ _
  }

isRoutingAlgebra : IsRoutingAlgebra Aʷⁱᵈᵉˢᵗ
isRoutingAlgebra = record
  { ⊕-sel        = ⊔-sel
  ; ⊕-comm       = ⊔-comm
  ; ⊕-assoc      = ⊔-assoc
  ; ⊕-zeroʳ       = ⊔-zeroʳ
  ; ⊕-identityʳ   = ⊔-identityʳ
  ; ▷-fixedPoint = ⊓-zeroʳ
  }

isDistributive : IsDistributive Aʷⁱᵈᵉˢᵗ
isDistributive = ⊓-distribˡ-⊔
