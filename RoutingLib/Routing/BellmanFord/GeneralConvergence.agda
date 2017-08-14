open import Data.Product using (∃; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_; s≤s; _<_; _≤_; _≤?_; _∸_)
open import Data.Nat.Properties using (m≤m+n; m+n∸m≡n)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions
open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Theorems using (module Guerney)
open import RoutingLib.Data.Nat.Properties using (suc-injective; m≤n⇨m+o≡n; ≰⇒≥; +-comm; +-assoc)

module RoutingLib.Routing.BellmanFord.GeneralConvergence
  {a b ℓ n-1} 
  (𝓡𝓟 : RoutingProblem a b ℓ (suc n-1)) 
  (sc : SufficientConditions (RoutingProblem.ra 𝓡𝓟))
  where

  open RoutingProblem 𝓡𝓟

  ------------------------------------------------------------------------
  -- Theorem
  --
  -- Distributed Bellman Ford over any RoutingAlgebra converges from 
  -- any state when it is possible to enumerate all values of Route

  open import RoutingLib.Routing.BellmanFord 𝓡𝓟

  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step2_Ultrametric 𝓡𝓟 sc using (d; dₘₐₓ; d-isUltrametric) public
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step3_StrictlyContracting 𝓡𝓟 sc using (σ-strictlyContractingOnOrbits)
  
  postulate d-satisfiesUltrametricConditions : Guerney.UltrametricConditions σ∥ d
{-
  d-satisfiesUltrametricConditions = record
    { isUltrametric               = {!!} --d-isUltrametric
    ; strictlyContractingOnOrbits = σ-strictlyContractingOnOrbits
    ; finiteImage                 = suc hₘₐₓ , d≤H
    }
-}

  σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
  σ-isAsynchronouslySafe = Guerney.StrictlyContractingUltrametric⇒AsynchronouslySafe σ∥ (d , d-satisfiesUltrametricConditions)

