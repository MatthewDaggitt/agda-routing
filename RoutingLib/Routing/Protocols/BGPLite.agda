import RoutingLib.Routing.VectorBased.Asynchronous.Convergence as Convergence
import RoutingLib.Routing.VectorBased.Asynchronous as VectorBasedRouting

open import RoutingLib.Iteration.Asynchronous.Dynamic using (Epoch; Convergent)

open import RoutingLib.Routing
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Protocols.BGPLite.Algebra

module RoutingLib.Routing.Protocols.BGPLite
  {n} (network : Network algebra n) where

open BellmanFord algebra network public using (δ∥)

-----------------
-- Convergence --
-----------------

δ-convergesAbsolutely : IsSafe δ∥
δ-convergesAbsolutely = ConvergenceTheorems.incrPaths-converges algebra isIncreasingPathAlgebra network

{-
σ-convergesIn-n² : {!!}
σ-convergesIn-n² = {!!}
-}
