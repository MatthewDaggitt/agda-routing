open import Relation.Binary using (Setoid)

module RoutingLib.Function.FixedPoint {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  FixedPoint : (A → A) → A → Set ℓ
  FixedPoint f x = f x ≈ x
