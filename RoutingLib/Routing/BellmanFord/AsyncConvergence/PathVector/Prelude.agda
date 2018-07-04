open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra
  as IncreasingPathAlgebraProperties
import RoutingLib.Routing.BellmanFord as BellmanFord
import RoutingLib.Routing.BellmanFord.Properties as BellmanFordProperties
import RoutingLib.Routing.BellmanFord.PathProperties as BellmanFordPathProperties
import RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra.Consistency as Consistency

module RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Prelude
  {a b ℓ n} (algebra : IncreasingPathAlgebra a b ℓ n)
  where

  open IncreasingPathAlgebra algebra public
  open IncreasingPathAlgebraProperties algebra public
 
  open BellmanFord rawRoutingAlgebra A public
  open BellmanFordProperties routingAlgebra A public
  open BellmanFordPathProperties pathAlgebra public

  open Consistency algebra public
