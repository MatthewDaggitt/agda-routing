open import Level using (_⊔_)
open import Relation.Binary using (Setoid; Rel)
open import Data.List
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.List.All using (All₂; []; _∷_)



module RoutingLib.Data.List.Equality {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  
  _≈ₗ_ : Rel (List A) (a ⊔ ℓ)
  xs ≈ₗ ys = All₂ _≈_ xs ys
