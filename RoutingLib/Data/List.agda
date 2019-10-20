
module RoutingLib.Data.List where

open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.List hiding (downFrom)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _⊓_; _⊔_; _≤_; _<_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; id)
open import Level
open import Relation.Binary using (Rel; Total)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)

private
  variable
    a b c ℓ : Level
    A : Set a
    B : Set b
    C : Set c

-----------
-- Other --
-----------

module _ {_≤_ : Rel A ℓ} (total : Total _≤_) where

  insert : A → List A → List A
  insert v []       = [ v ]
  insert v (x ∷ xs) with total v x
  ... | inj₁ v≤x = v ∷ x ∷ xs
  ... | inj₂ x≤v = x ∷ insert v xs

  merge : List A → List A → List A
  merge []       ys       = ys
  merge xs       []       = xs
  merge (x ∷ xs) (y ∷ ys) with total x y
  ... | inj₁ x≤y = x ∷ merge xs (y ∷ ys)
  ... | inj₂ y≤x = y ∷ merge (x ∷ xs) ys

combine : (A → B → C) → List A → List B → List C
combine f []       _  = []
combine f (x ∷ xs) ys = map (f x) ys ++ combine f xs ys

allPairs : List A → List B → List (A × B)
allPairs = combine _,_

allFinPairs : ∀ n → List (Fin n × Fin n)
allFinPairs n = allPairs (allFin n) (allFin n)
