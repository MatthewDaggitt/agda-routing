open import Level using (_⊔_)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (∃; _×_)

open import RoutingLib.Function.Metric
open import RoutingLib.Function.Metric.Contraction

module RoutingLib.Asynchronous.Theorems (n : ℕ) where

  open import RoutingLib.Asynchronous


  -- Guerney's theorem
  module Guerney {a ℓ n} (f : Parallelisation a ℓ n) where

    open Parallelisation f

    record UltrametricConditions (d : M → M → ℕ) : Set (a ⊔ ℓ) where
      field
        isUltrametric : IsUltrametric Sₘ d
        strictlyContractingOnOrbits : StrictlyContractingOnOrbits Sₘ d σ
        finiteImage : ∃ λ n → ∀ x y → d x y ≤ n
        
    postulate StrictlyContractingUltrametric⇒AsynchronouslySafe : (∃ λ d → UltrametricConditions d) → IsAsynchronouslySafe f
    
    postulate AsynchronouslySafe⇒StrictlyContractingUltrametric : IsAsynchronouslySafe f → (∃ λ d → UltrametricConditions d)
