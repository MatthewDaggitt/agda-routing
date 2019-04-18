--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the definition of the algebra underlying a path
-- vector protocol that solves the shortest paths problem, i.e. tries to find
-- the paths with shortest length/lowest latency.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.PathVector.ShortestWidestPaths where

open import Algebra.FunctionProperties using (Op₂)
open import Data.Product using (_×_; _,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Construct.AddPaths as AddPaths
  using (AddPaths)
open import RoutingLib.Routing.Protocols.DistanceVector.ShortestWidestPaths

open IsRoutingAlgebra isRoutingAlgebra 

--------------------------------------------------------------------------------
-- Algebra definition

Aˢʷᵖ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aˢʷᵖ = AddPaths Aˢʷ ⊕-assoc ⊕-sel ⊕-comm 

--------------------------------------------------------------------------------
-- Properties of the algebra

Aˢʷᵖ-isPathAlgebra : IsPathAlgebra Aˢʷᵖ
Aˢʷᵖ-isPathAlgebra = AddPaths.isPathAlgebra Aˢʷ ⊕-assoc ⊕-sel ⊕-comm 

open PathDistributivity Aˢʷᵖ-isPathAlgebra
