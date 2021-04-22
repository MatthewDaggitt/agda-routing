--------------------------------------------------------------------------------
-- Agda routing library
--
-- A specification of a path-vector routing protocol that shares many
-- similarities with the Border Gateway Protocol (BGP), including local
-- preferences, conditional policy, community values, path inflation and more.
--
-- Unlike BGP this algebra is strictly increasing as the local preference value
-- cannot be set arbitarily. In addition it does not implement the MED attribute
-- that violates associativity.
--------------------------------------------------------------------------------

open import Data.Nat.Base using (_^_)

open import RoutingLib.Routing.VectorBased.Convergence.Results
open import RoutingLib.Routing.Protocols.BGPLite.Simulation

module RoutingLib.Routing.Protocols.BGPLite where

--------------------------------------------------------------------------------
-- Core definition

open import RoutingLib.Routing.Protocols.BGPLite.PathWeights public
open import RoutingLib.Routing.Protocols.BGPLite.Communities public
open import RoutingLib.Routing.Protocols.BGPLite.Policies public
open import RoutingLib.Routing.Protocols.BGPLite.Core public

--------------------------------------------------------------------------------
-- The algebra always converges (proved via simulation with an equivalent but
-- better behaved routing algebra).

δ-convergent : Convergent A
δ-convergent = simulate-convergent Aₐₗₜ-simulates-A Aₐₗₜ-convergent

σ-converges-O[n²] : SynchronouslyConvergesIn A (λ n → n ^ 2)
σ-converges-O[n²] = simulate-syncConvergesIn Aₐₗₜ-simulates-A (λ n → n ^ 2) Aₐₗₜ-syncConverges-O[n²]
