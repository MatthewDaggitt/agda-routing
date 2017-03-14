open import Level using (_⊔_)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (∃; _×_)

open import RoutingLib.Function.Metric
open import RoutingLib.Function.Metric.Contraction

module RoutingLib.Asynchronous.Theorems where

  open import RoutingLib.Asynchronous


  -- Guerney's theorem
  module Guerney {a ℓ n} (p : Parallelisation a ℓ n) where

    open Parallelisation p
    open import RoutingLib.Asynchronous.Properties p

    record UltrametricConditions (d : M → M → ℕ) : Set (a ⊔ ℓ) where
      field
        isUltrametric               : IsUltrametric Sₘ d
        strictlyContractingOnOrbits : StrictlyContractingOnOrbits Sₘ d σ
        finiteImage                 : ∃ λ n → ∀ x y → d x y ≤ n
        
    postulate StrictlyContractingUltrametric⇒AsynchronouslySafe : (∃ λ d → UltrametricConditions d) → IsAsynchronouslySafe p
    
    postulate AsynchronouslySafe⇒StrictlyContractingUltrametric : IsAsynchronouslySafe p → (∃ λ d → UltrametricConditions d)
