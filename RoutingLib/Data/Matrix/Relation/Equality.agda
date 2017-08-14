open import Data.Nat using (ℕ)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Matrix using (Matrix)
open import RoutingLib.Data.Matrix.Relation.Pointwise using (Pointwise; setoid)

module RoutingLib.Data.Matrix.Relation.Equality {a ℓ} (S : Setoid a ℓ) where

  open Setoid S using (_≈_) renaming (Carrier to A)

  _≈ₘ_ : ∀ {m n} → Rel (Matrix A m n) ℓ
  _≈ₘ_ = Pointwise _≈_
  
  _≉ₘ_ : ∀ {m n} → Rel (Matrix A m n) ℓ
  t ≉ₘ s = ¬ (t ≈ₘ s)

  𝕄ₛ : ℕ → ℕ → Setoid a ℓ
  𝕄ₛ m n = setoid S m n

  module _ {m n : ℕ} where
    open Setoid (𝕄ₛ m n) public using ()
      renaming
      ( reflexive     to ≈ₘ-reflexive
      ; refl          to ≈ₘ-refl
      ; sym           to ≈ₘ-sym
      ; trans         to ≈ₘ-trans
      ; isEquivalence to ≈ₘ-isEquivalence
      )
