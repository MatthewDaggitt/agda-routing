--------------------------------------------------------------------------------
-- This module constructs the static schedule that corresponds to the infinitely
-- asynchronous computation
--------------------------------------------------------------------------------
open import Data.Nat using (ℕ)

module RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Infinite {n : ℕ} where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊥)
open import Data.Fin.Subset.Properties using (_∈?_ ; ∉⊥)
open import Data.Nat using (zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Schedule

--------------------------------------------------------------------------------
-- Definition

α∞ : 𝕋 → Subset n
α∞ t = ⊥

β∞ : 𝕋 → Fin n → Fin n → 𝕋
β∞ t _ _ = zero

β∞-causality : ∀ t i j → β∞ (suc t) i j ≤ t
β∞-causality t _ _ = z≤n

ψ∞ : Schedule n
ψ∞ = record
  { α           = α∞
  ; β           = β∞
  ; β-causality = β∞-causality
  }

--------------------------------------------------------------------------------
-- Properties

module _ {a ℓ} (I∥ : AsyncIterable a ℓ n) where
  open AsyncIterable I∥

  ψ∞-isInfAsynchronous' : ∀ x₀ {t} (accₜ : Acc _<_ t) → asyncIter' I∥ ψ∞ x₀ accₜ ≈ x₀
  ψ∞-isInfAsynchronous' x₀ {zero} accₜ = ≈-refl
  ψ∞-isInfAsynchronous' x₀ {suc t} (acc rec) i with i ∈? α∞ (suc t)
  ... | no  i∉α = ψ∞-isInfAsynchronous' x₀ (rec t ≤-refl) i
  ... | yes i∈α = contradiction i∈α ∉⊥

  ψ∞-isInfAsynchronous : ∀ x₀ t → asyncIter I∥ ψ∞ x₀ t ≈ x₀
  ψ∞-isInfAsynchronous x₀ t = ψ∞-isInfAsynchronous' x₀ (<-wellFounded t)
