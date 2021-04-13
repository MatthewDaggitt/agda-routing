
module RoutingLib.Data.List where

open import Algebra using (Op₂; Selective)
open import Data.List hiding (downFrom)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _⊓_; _⊔_; _≤_; _<_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; id)
open import Level
open import Relation.Binary as B hiding (Decidable)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

private
  variable
    a b c p ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

-----------
-- Other --
-----------

module _ {_<_ : Rel A ℓ₂} {_≈_ : Rel A ℓ₃} (<-cmp : Trichotomous _≈_ _<_) (_⊕_ : Op₂ A) where

  partialMerge : List A → List A → List A
  partialMerge []       ys       = ys
  partialMerge (x ∷ xs) []       = x ∷ xs
  partialMerge (x ∷ xs) (y ∷ ys) with <-cmp x y
    | partialMerge xs (y ∷ ys)
    | partialMerge (x ∷ xs) ys
    | partialMerge xs ys
  ... | tri< _ _ _ | rec₁ | _    | _    = x ∷ rec₁
  ... | tri> _ _ _ | _    | rec₂ | _    = y ∷ rec₂
  ... | tri≈ _ _ _ | _    | _    | rec₃ = (x ⊕ y) ∷ rec₃

allFinPairs : ∀ n → List (Fin n × Fin n)
allFinPairs n = cartesianProduct (allFin n) (allFin n)
