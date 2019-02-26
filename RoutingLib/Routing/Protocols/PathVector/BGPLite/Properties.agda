

module RoutingLib.Routing.Protocols.PathVector.BGPLite.Properties where

open import Data.Nat using (ℕ; _≟_; _^_)

open import RoutingLib.Routing.Protocols.PathVector.BGPLite

--------------------------------------------------------------------------------
-- The algebra always converges (proved via a simulation with an equivalent but
-- better behaved routing algebra).

open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Simulation
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence

δ-alwaysConvergent : AlwaysConvergent A
δ-alwaysConvergent = simulate Aₐₗₜ-simulates-A Aₐₗₜ-alwaysConvergent
