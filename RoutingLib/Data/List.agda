open import Data.List
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

module RoutingLib.Data.List where

  allFin : ∀ n → List (Fin n)
  allFin zero    = []
  allFin (suc n) = fzero ∷ map fsuc (allFin n)

  descending : ∀ n → List ℕ
  descending zero    = []
  descending (suc n) = n ∷ descending n


  combine : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
         → (A → B → C) → List A → List B → List C
  combine f [] _ = []
  combine f (x ∷ xs) ys = map (f x) ys ++ combine f xs ys
