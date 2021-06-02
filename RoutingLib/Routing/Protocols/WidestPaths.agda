--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the definition of the algebra underlying a distance
-- vector protocol that solves the widest paths problem, i.e. tries to find the
-- paths with highest bandwidth.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.WidestPaths where

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; cong)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties

open import RoutingLib.Routing.Algebra

--------------------------------------------------------------------------------
-- Algebra
