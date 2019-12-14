open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open import RoutingLib.Iteration.Synchronous

module RoutingLib.Iteration.Synchronous.Properties {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A; refl to ≈-refl)

^-congʳ : ∀ f {n n'} → n ≡ n' → ∀ x → (f ^ n) x ≈ (f ^ n') x
^-congʳ f refl x = ≈-refl
