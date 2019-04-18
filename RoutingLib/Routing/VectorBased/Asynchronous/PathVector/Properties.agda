open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing using (AdjacencyMatrix)

module RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Properties
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Properties as DistanceVectorProperties
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Properties as CorePathProperties

open IsCertifiedPathAlgebra isPathAlgebra

------------------------------------------------------------------------
-- Publicly re-export core properties

open DistanceVectorProperties isRoutingAlgebra public
open CorePathProperties isRoutingAlgebra isPathAlgebra A public

