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

open import RoutingLib.Routing.VectorBased.Asynchronous.Results

module RoutingLib.Routing.Protocols.BGPLite where

--------------------------------------------------------------------------------
-- Core definition

open import RoutingLib.Routing.Protocols.BGPLite.Routes public
open import RoutingLib.Routing.Protocols.BGPLite.Communities public
open import RoutingLib.Routing.Protocols.BGPLite.Policies public
open import RoutingLib.Routing.Protocols.BGPLite.Core public

--------------------------------------------------------------------------------
-- The algebra always converges (proved via simulation with an equivalent but
-- better behaved routing algebra).

open import RoutingLib.Routing.Protocols.BGPLite.Simulation

δ-alwaysConvergent : Convergent A
δ-alwaysConvergent = simulate Aₐₗₜ-simulates-A Aₐₗₜ-convergent
