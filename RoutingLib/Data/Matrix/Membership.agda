open import Relation.Binary using (Setoid)

open import RoutingLib.Data.Matrix

module RoutingLib.Data.Matrix.Membership {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  _∈_ : A → ∀ {m n} → Matrix A m n → Set _
  x ∈ M = Any (x ≈_) M
