open import Relation.Binary using (Setoid)

open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Unary.Any

module RoutingLib.Data.Vec.Functional.Membership {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

_∈_ : ∀ {n} → A → Vector A n → Set _
x ∈ t = Any (x ≈_) t

_⊆_ : ∀ {n} → Vector A n → Vector A n → Set _
s ⊆ t = ∀ {x} → x ∈ s → x ∈ t
