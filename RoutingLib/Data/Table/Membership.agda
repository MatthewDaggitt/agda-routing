open import Relation.Binary using (Setoid)

open import RoutingLib.Data.Table

module RoutingLib.Data.Table.Membership {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  
  _∈_ : ∀ {n} → A → Table A n → Set _
  x ∈ t = Any (x ≈_) t
