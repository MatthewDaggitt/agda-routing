open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)
open import Data.Fin.Dec using (all?)
open import Data.Nat using (ℕ; suc)

open import RoutingLib.Data.Table

module RoutingLib.Data.Table.Properties where

{-
  zipWith-sym : ∀ {a b ℓ} {A : Set a} {B : Set b}
                {_⊕_ : A → A → B} {_≈_ : Rel B ℓ} →
                (∀ x y → (x ⊕ y) ≡ (y ⊕ x)) →
                ∀ {n} (t s : Table A n) → zipWith _⊕_ t s ≡ zipWith _⊕_ s t
  zipWith-sym sym t s = {!!}
-}
