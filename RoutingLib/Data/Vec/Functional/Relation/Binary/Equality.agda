open import Relation.Binary using (DecSetoid; Setoid; Rel)

module RoutingLib.Data.Vec.Functional.Relation.Binary.Equality {a ℓ} (S : Setoid a ℓ) where

open import Data.Vec.Functional
open import Data.Nat using (ℕ)
open import Relation.Binary.Indexed.Homogeneous
  using (IndexedSetoid)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Vec.Functional.Relation.Binary.Pointwise using (setoid)

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

_≉ₜ_ : ∀ {n} → Rel (Vector A n) ℓ
t ≉ₜ s = ¬ (t ≈ₜ s)
