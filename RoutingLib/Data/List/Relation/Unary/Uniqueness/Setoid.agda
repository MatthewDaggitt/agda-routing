open import Level using (_⊔_)
open import Data.List using (List)
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)

module RoutingLib.Data.List.Relation.Unary.Uniqueness.Setoid {c ℓ} (S : Setoid c ℓ) where

  open Setoid S renaming (Carrier to A)
  open import RoutingLib.Data.List.Relation.Unary.AllPairs using ([]; _∷_) public

  Unique : List A → Set (c ⊔ ℓ)
  Unique xs = AllPairs (λ x y → ¬ (x ≈ y)) xs
