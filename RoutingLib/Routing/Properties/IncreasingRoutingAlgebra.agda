open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Properties.RoutingAlgebra as RoutingAlgebraProperties

module RoutingLib.Routing.Properties.IncreasingRoutingAlgebra
  {a b ℓ} (algebra : IncreasingRoutingAlgebra a b ℓ) where

open IncreasingRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Increasing path algebra

open RoutingAlgebraProperties routingAlgebra public
