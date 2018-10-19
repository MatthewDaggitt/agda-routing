open import RoutingLib.Data.Matrix using (SquareMatrix)
open import Data.Nat using (zero; suc; s≤s; z≤n; _^_; _+_; _≤_)
open import Function using (case_of_)

open import RoutingLib.Routing.Algebra
import RoutingLib.Function.Iteration.Convergence as Convergence

import RoutingLib.Routing.BellmanFord.Synchronous as BellmanFord
open import RoutingLib.Routing.BellmanFord.ConvergenceConditions


module RoutingLib.Routing.BellmanFord.Synchronous.Results
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open BellmanFord algebra
    
--------------------------------------------------------------------------------
-- Theorem 3
--
-- σ is always guaranteed to converge synchronously in n² steps over any
-- increasing path algebra

module _ (conditions : IsIncreasingPathAlgebra algebra) where

  open IsIncreasingPathAlgebra conditions
  
  σ-convergesIn-n² : ∀ {n} (A : AdjacencyMatrix algebra n) → (σ A) ConvergesIn (n ^ 2)
  σ-convergesIn-n² = {!!}
{-
  {zero}    A X t ()
  σ-convergesIn-n² {suc n-1} A = n²-convergence
    where
    open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Prelude (isCertifiedPathAlgebra (suc n-1)) A
    open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step5_Proof (isCertifiedPathAlgebra (suc n-1)) isIncreasing A
-}
