open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Properties.PathAlgebra
  as PathAlgebraProperties

module RoutingLib.Routing.Properties.IncreasingPathAlgebra
  {a b ℓ n} (algebra : IncreasingPathAlgebra a b ℓ n) where

open IncreasingPathAlgebra algebra

--------------------------------------------------------------------------------
-- Open path algebra properties

open PathAlgebraProperties pathAlgebra public
