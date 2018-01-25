open import Data.List
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary

module RoutingLib.Data.List.Sorting.Bubblesort
  {a ℓ₁ ℓ₂} (DTO : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder DTO renaming (Carrier to A)
  
  bubble : List A → List A
  bubble []           = []
  bubble (x ∷ [])     = x ∷ []
  bubble (x ∷ y ∷ xs) with total x y
  ... | inj₁ x≤y = x ∷ bubble (y ∷ xs)
  ... | inj₂ y≤x = y ∷ bubble (x ∷ xs)

  bubblesort : List A → List A
  bubblesort []       = []
  bubblesort (x ∷ xs) = {!!}
