open import Data.Nat using (ℕ)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Table
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise; setoid)

module RoutingLib.Data.Table.Relation.Equality {a ℓ} (S : Setoid a ℓ) where

  open Setoid S using (_≈_) renaming (Carrier to A)

  𝕋ₛ : ℕ → Setoid a ℓ
  𝕋ₛ n = setoid S n

  module _ {n : ℕ} where
    open Setoid (𝕋ₛ n) public using ()
      renaming
      ( _≈_           to _≈ₜ_
      ; reflexive     to ≈ₜ-reflexive
      ; refl          to ≈ₜ-refl
      ; sym           to ≈ₜ-sym
      ; trans         to ≈ₜ-trans
      ; isEquivalence to ≈ₜ-isEquivalence
      )

  _≉ₜ_ : ∀ {n} → Rel (Table A n) ℓ
  t ≉ₜ s = ¬ (t ≈ₜ s)
