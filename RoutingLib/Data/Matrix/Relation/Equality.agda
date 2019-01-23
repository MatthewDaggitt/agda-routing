open import Data.Nat using (ℕ)
open import Data.Fin.Subset using (Subset; _∉_; ∣_∣)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Matrix.Relation.Pointwise as PW using (Pointwise)

module RoutingLib.Data.Matrix.Relation.Equality {a ℓ} (S : Setoid a ℓ) where

open Setoid S using (_≈_; refl) renaming (Carrier to A)

_≈ₘ_ : ∀ {m n} → Rel (Matrix A m n) ℓ
_≈ₘ_ = Pointwise _≈_

_≉ₘ_ : ∀ {m n} → Rel (Matrix A m n) ℓ
t ≉ₘ s = ¬ (t ≈ₘ s)

𝕄ₛ : ℕ → ℕ → Setoid a ℓ
𝕄ₛ m n = PW.setoid S m n

module _ {m n : ℕ} where
  open Setoid (𝕄ₛ m n) public using ()
    renaming
    ( reflexive     to ≈ₘ-reflexive
    ; refl          to ≈ₘ-refl
    ; sym           to ≈ₘ-sym
    ; trans         to ≈ₘ-trans
    ; isEquivalence to ≈ₘ-isEquivalence
    )

{-
module _ {m n} (p : Subset m) (q : Subset n) where

  grow-strip : (T : Matrix A m n) (M : Matrix A m n) →
               (∀ {i j} → i ∉ p → j ∉ q → T i j ≈ M i j) →
               grow p q T (strip p q M) ≈ₘ M
  grow-strip = PW.grow-strip {_~_ = _≈_} refl p q

  strip-grow : (T : Matrix A m n) (M : Matrix A ∣ p ∣ ∣ q ∣) →
               strip p q (grow p q T M) ≈ₘ M
  strip-grow = PW.strip-grow {_~_ = _≈_} refl p q
-}
