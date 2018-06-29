open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra
  as IncreasingPathAlgebraProperties

module RoutingLib.Routing.Algebra.Properties.StrictlyIncreasingPathAlgebra
  {a b ℓ n} (algebra : StrictlyIncreasingPathAlgebra a b ℓ n) where

open StrictlyIncreasingPathAlgebra algebra

--------------------------------------------------------------------------------
-- Open increasing path algebra properties

open IncreasingPathAlgebraProperties increasingPathAlgebra public
  hiding (▷-strictlyIncreasing)
