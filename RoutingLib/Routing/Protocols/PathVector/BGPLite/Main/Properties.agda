--------------------------------------------------------------------------------
-- Agda routing library
--
-- Properties of the main BGPLite algebra. Includes a proof that it is
-- convergent.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.PathVector.BGPLite.Main.Properties where

open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Main
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Simulation.Properties
open import RoutingLib.Routing.VectorBased.Asynchronous.Results

--------------------------------------------------------------------------------
-- The algebra always converges (proved via a simulation with an equivalent but
-- better behaved routing algebra).

δ-alwaysConvergent : Convergent A
δ-alwaysConvergent = simulate Aₐₗₜ-simulates-A Aₐₗₜ-convergent
