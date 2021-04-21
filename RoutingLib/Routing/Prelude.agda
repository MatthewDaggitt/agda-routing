--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module re-exports all the basic definitions to do with routing over a
-- particular routing algebra and network size.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra
open import Data.Nat using (ℕ)

module RoutingLib.Routing.Prelude
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  (n : ℕ)
  where

open import RoutingLib.Routing.Basics.Node n public
open import RoutingLib.Routing.Basics.Network algebra n public
open import RoutingLib.Routing.Basics.State algebra n public

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule public
  using (Epoch)
