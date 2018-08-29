import RoutingLib.Routing.BellmanFord.Theorems as ConvergenceTheorems
import RoutingLib.Routing.BellmanFord as BellmanFord

open import RoutingLib.Asynchronous
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Protocols.BGPLite.Algebra

module RoutingLib.Routing.Protocols.BGPLite
  {n} (A : AdjacencyMatrix algebra n) where

open BellmanFord algebra A public using (σ; δ; σ^; σ∥)

-----------------
-- Convergence --
-----------------

δ-convergesAbsolutely : IsAsynchronouslySafe σ∥
δ-convergesAbsolutely = ConvergenceTheorems.incrPaths-converges algebra isIncreasingPathAlgebra A

σ-convergesIn-n² : {!!}
σ-convergesIn-n² = {!!}
