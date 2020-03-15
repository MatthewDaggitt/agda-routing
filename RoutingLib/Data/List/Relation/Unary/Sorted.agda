open import Level using (_⊔_)
open import Data.List using (List; length; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Unique.Setoid using (Unique)
open import Relation.Binary using (TotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)


module RoutingLib.Data.List.Relation.Unary.Sorted
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open TotalOrder totalOrder
  renaming (Carrier to A)

Sorted : List A → Set (a ⊔ ℓ₂)
Sorted xs = AllPairs _≤_ xs
