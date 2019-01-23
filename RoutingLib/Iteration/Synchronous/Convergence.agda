open import Data.Nat using (ℕ; _≤_; _+_)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning

--open import RoutingLib.Function.Iteration

module RoutingLib.Iteration.Synchronous.Convergence
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open EqReasoning S

_ConvergesIn_ : (A → A) → ℕ → Set _
f ConvergesIn n = ∀ x t → (f ^ˡ n) x ≈ (f ^ˡ (n + t)) x

{-
ConvergesIn-mono : ∀ f {n m} → n ≤ m → f ConvergesIn n → f ConvergesIn m
ConvergesIn-mono f {n} {m} n≤m conv x t = begin
  (f ^ˡ m)       x ≈⟨ {!∼!} ⟩
  (f ^ˡ n)       x ≈⟨ {!!} ⟩
  (f ^ˡ (m + t)) x ∎
-}
