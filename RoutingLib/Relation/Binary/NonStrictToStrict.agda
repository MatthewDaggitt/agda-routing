
open import Relation.Binary using (Rel; Symmetric; Transitive)
open import Relation.Nullary using (¬_)
open import Data.Product using (_,_)


module RoutingLib.Relation.Binary.NonStrictToStrict {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) where

  open import Relation.Binary.NonStrictToStrict _≈_ _≤_
  open import RoutingLib.Relation.Binary.RespectedBy
  
  <-resp-by-≈ : Symmetric _≈_ → Transitive _≈_ → _≤_ RespectedBy _≈_ → _<_ RespectedBy _≈_
  <-resp-by-≈ sym trans ≤-resp-≈ a≈b c≈d (a≤c , a≉c) = (≤-resp-≈ a≈b c≈d a≤c) , (λ b≈d → a≉c (trans (trans a≈b b≈d) (sym c≈d)))

