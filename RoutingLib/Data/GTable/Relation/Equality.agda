open import Data.Nat using (ℕ)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.GTable
open import RoutingLib.Data.GTable.Relation.Pointwise using (Pointwise; setoid)

module RoutingLib.Data.GTable.Relation.Equality {a ℓ n} (S : Table (Setoid a ℓ) n) where

  --open Setoid S using (_≈_) renaming (Carrier to A)

  𝔾𝕋ₛ : ℕ → Setoid a ℓ
  𝔾𝕋ₛ n = setoid S n

  open Setoid (𝔾𝕋ₛ n) public using ()
      renaming
      ( _≈_           to _≈ₜ_
      ; reflexive     to ≈ₜ-reflexive
      ; refl          to ≈ₜ-refl
      ; sym           to ≈ₜ-sym
      ; trans         to ≈ₜ-trans
      ; isEquivalence to ≈ₜ-isEquivalence
      )
      
  --_≉ₜ_ : ∀ {n} → Rel (GTable n ?) ℓ
  --t ≉ₜ s = ¬ (t ≈ₜ s)
