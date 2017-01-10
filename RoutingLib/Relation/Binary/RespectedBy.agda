
open import Relation.Binary
open import Data.Product using (_,_)

module RoutingLib.Relation.Binary.RespectedBy {a ℓ₁ ℓ₂} {A : Set a} where

  -- A more general version of stdlib's _Respects₂_ which is much easier to work with...
  _RespectedBy_ : Rel A ℓ₁ → Rel A ℓ₂ → Set _
  _~_ RespectedBy _≈_ = ∀ {a b c d} → a ≈ b → c ≈ d → a ~ c → b ~ d

  RespectedBy⇨Respects₂ : ∀ {_≈_ : Rel A ℓ₂} {_~_ : Rel A ℓ₁} → Reflexive _≈_ → _~_ RespectedBy _≈_ → _~_ Respects₂ _≈_
  RespectedBy⇨Respects₂ ≈-refl ~-respectedby-≈ = (~-respectedby-≈ ≈-refl) , (λ pr → ~-respectedby-≈ pr ≈-refl)

  Respects₂⇨RespectedBy : ∀ {_≈_ : Rel A ℓ₂} {_~_ : Rel A ℓ₁} → _~_ Respects₂ _≈_ → _~_ RespectedBy _≈_
  Respects₂⇨RespectedBy (t , s) a≈b c≈d a~c = t c≈d (s a≈b a~c)
