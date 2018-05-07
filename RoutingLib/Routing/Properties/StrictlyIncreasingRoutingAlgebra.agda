open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Properties.IncreasingRoutingAlgebra
  as IncreasingRoutingAlgebraProperties

module RoutingLib.Routing.Properties.StrictlyIncreasingRoutingAlgebra
  {a b ℓ} (algebra : StrictlyIncreasingRoutingAlgebra a b ℓ) where

open StrictlyIncreasingRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Increasing path algebra

open IncreasingRoutingAlgebraProperties increasingRoutingAlgebra public
