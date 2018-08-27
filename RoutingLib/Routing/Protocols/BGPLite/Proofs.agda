import RoutingLib.Routing.BellmanFord.Theorems as ConvergenceTheorems
import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.Protocols.BGPLite.Proofs where



-----------------
-- Convergence --
-----------------

open BellmanFord rawRoutingAlgebra A

δ-convergesAbsolutely : IsAsynchronouslySafe σ∥
δ-convergesAbsolutely = ConvergenceTheorems.incrPaths-converges increasingPathAlgebra
