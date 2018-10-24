import RoutingLib.Routing.BellmanFord.Asynchronous.Results as ConvergenceTheorems
import RoutingLib.Routing.BellmanFord.Asynchronous as BellmanFord

open import RoutingLib.Iteration.Asynchronous.Dynamic using (IsSafe)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)

open import RoutingLib.Routing.Model
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Protocols.BGPLite.Algebra

module RoutingLib.Routing.Protocols.BGPLite
  {n} (network : Epoch → AdjacencyMatrix algebra n) where

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
