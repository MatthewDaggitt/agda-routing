open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Level using (_⊔_) renaming (zero to ℓ₀)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra.Consistency
  as IncreasingConsistency
import RoutingLib.Routing.Algebra.Properties.StrictlyIncreasingPathAlgebra
  as StrictlyIncreasingPathAlgebraProperties

module RoutingLib.Routing.Algebra.Properties.StrictlyIncreasingPathAlgebra.Consistency
  {a b ℓ n} (algebra : StrictlyIncreasingPathAlgebra a b ℓ n)
  where

open StrictlyIncreasingPathAlgebra algebra

------------------------------------------------------------------------------
-- Open increasing path algebra consistency

open IncreasingConsistency increasingPathAlgebra public
