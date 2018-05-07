open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Level using (_⊔_) renaming (zero to ℓ₀)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Properties.IncreasingPathAlgebra.Consistency
  as IncreasingConsistency
import RoutingLib.Routing.Properties.StrictlyIncreasingPathAlgebra
  as StrictlyIncreasingPathAlgebraProperties

module RoutingLib.Routing.Properties.StrictlyIncreasingPathAlgebra.Consistency
  {a b ℓ n} (algebra : StrictlyIncreasingPathAlgebra a b ℓ n)
  where

open StrictlyIncreasingPathAlgebra algebra
open StrictlyIncreasingPathAlgebraProperties algebra

------------------------------------------------------------------------------
-- Open increasing path algebra consistency

open IncreasingConsistency increasingPathAlgebra public

------------------------------------------------------------------------------
-- New properties

▷ᶜ-strictlyIncreasing : ∀ (s : CStep) {r : CRoute} → r ≉ᶜ (∞ , ∞ᶜ) →
                        ((s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r) × (r ≉ᶜ (s ▷ᶜ r))
▷ᶜ-strictlyIncreasing (i , j) r≉∞ = ▷-strictlyIncreasing (A i j) r≉∞

------------------------------------------------------------------------------
-- Algebra

isStrictlyIncreasingRoutingAlgebraᶜ : IsStrictlyIncreasingRoutingAlgebra _≈ᶜ_ _⊕ᶜ_ _▷ᶜ_ C0# C∞
isStrictlyIncreasingRoutingAlgebraᶜ = record
  { isRoutingAlgebra     = isRoutingAlgebraᶜ
  ; ▷-strictlyIncreasing = ▷ᶜ-strictlyIncreasing
  }
  
strictlyIncreasingRoutingAlgebraᶜ : StrictlyIncreasingRoutingAlgebra ℓ₀ (b ⊔ ℓ) ℓ
strictlyIncreasingRoutingAlgebraᶜ = record
  { isStrictlyIncreasingRoutingAlgebra = isStrictlyIncreasingRoutingAlgebraᶜ
  }
  
isFiniteStrictlyIncreasingRoutingAlgebraᶜ : IsFiniteStrictlyIncreasingRoutingAlgebra _≈ᶜ_ _⊕ᶜ_ _▷ᶜ_ C0# C∞
isFiniteStrictlyIncreasingRoutingAlgebraᶜ = record
  { isStrictlyIncreasingRoutingAlgebra = isStrictlyIncreasingRoutingAlgebraᶜ
  ; allRoutes                          = allCRoutes
  ; ∈-allRoutes                        = ∈-allCRoutes
  }

finiteStrictlyIncreasingRoutingAlgebraᶜ : FiniteStrictlyIncreasingRoutingAlgebra ℓ₀ (b ⊔ ℓ) ℓ
finiteStrictlyIncreasingRoutingAlgebraᶜ = record
  { isFiniteStrictlyIncreasingRoutingAlgebra = isFiniteStrictlyIncreasingRoutingAlgebraᶜ
  }
