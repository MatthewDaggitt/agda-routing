open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Properties.StrictlyIncreasingPathAlgebra
  as StrictlyIncreasingPathAlgebraProperties
import RoutingLib.Routing.BellmanFord as BellmanFord
import RoutingLib.Routing.BellmanFord.Properties as BellmanFordProperties
import RoutingLib.Routing.BellmanFord.PathProperties as BellmanFordPathProperties
import RoutingLib.Routing.Properties.StrictlyIncreasingPathAlgebra.Consistency as Consistency

module RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Prelude
  {a b ℓ n} (algebra : StrictlyIncreasingPathAlgebra a b ℓ n)
  where

  open StrictlyIncreasingPathAlgebra algebra public
  open StrictlyIncreasingPathAlgebraProperties algebra public
 
  open BellmanFord rawRoutingAlgebra A public
  open BellmanFordProperties routingAlgebra A public
  open BellmanFordPathProperties pathAlgebra public

  open Consistency algebra public
