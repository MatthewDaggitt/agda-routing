
module RoutingLib.Data.List where

open import Algebra using (Op₂)
open import Data.List hiding (downFrom)
open import Data.Fin using (Fin)
open import Data.Product using (_,_; _×_)
open import Level using (Level)
open import Relation.Binary 

private
  variable
    a b c p ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set a

-----------
-- Other --
-----------

module _ {_<_ : Rel A ℓ₂} {_≈_ : Rel A ℓ₃} (<-cmp : Trichotomous _≈_ _<_) (_⊕_ : Op₂ A) where

  partialMerge : List A → List A → List A
  partialMerge []       ys       = ys
  partialMerge (x ∷ xs) []       = x ∷ xs
  partialMerge (x ∷ xs) (y ∷ ys) with <-cmp x y | partialMerge xs (y ∷ ys)
  ... | tri< _ _ _ | rec₁ = x ∷ rec₁
  ... | tri> _ _ _ | _    = y ∷ partialMerge (x ∷ xs) ys
  ... | tri≈ _ _ _ | _    = (x ⊕ y) ∷ partialMerge xs ys

allFinPairs : ∀ n → List (Fin n × Fin n)
allFinPairs n = cartesianProduct (allFin n) (allFin n)
