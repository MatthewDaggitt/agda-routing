open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Properties
  as PathAlgebraProperties
import RoutingLib.Routing.BellmanFord as BellmanFord
import RoutingLib.Routing.BellmanFord.Properties as BellmanFordProperties
import RoutingLib.Routing.BellmanFord.PathProperties as BellmanFordPathProperties
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Consistency as Consistency

module RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Prelude
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

  open RawRoutingAlgebra algebra public
  open IsCertifiedPathAlgebra isPathAlgebra public
  open PathAlgebraProperties algebra isPathAlgebra public

  open BellmanFord algebra A public
  open BellmanFordProperties algebra isRoutingAlgebra A public
  open BellmanFordPathProperties algebra isPathAlgebra A public
  
  open Consistency algebra isPathAlgebra A public
