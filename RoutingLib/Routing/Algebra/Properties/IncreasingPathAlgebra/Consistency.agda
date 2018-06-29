open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Level using (_⊔_) renaming (zero to ℓ₀)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.PathAlgebra.Consistency as Consistency
import RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra
  as IncreasingPathAlgebraProperties

module RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra.Consistency
  {a b ℓ n} (algebra : IncreasingPathAlgebra a b ℓ n)
  where

open IncreasingPathAlgebra algebra
open IncreasingPathAlgebraProperties algebra

------------------------------------------------------------------------------
-- Open increasing path algebra consistency

open Consistency pathAlgebra public

------------------------------------------------------------------------------
-- New properties

▷ᶜ-increasing : ∀ s r → (s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r
▷ᶜ-increasing (i , j) (r , _) = ▷-increasing (A i j) r

▷ᶜ-strictlyIncreasing : ∀ (s : CStep) {r : CRoute} → r ≉ᶜ (∞ , ∞ᶜ) →
                        ((s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r) × (r ≉ᶜ (s ▷ᶜ r))
▷ᶜ-strictlyIncreasing (i , j) r≉∞ = ▷-strictlyIncreasing i j r≉∞

------------------------------------------------------------------------------
-- Routing algebra

isIncreasingRoutingAlgebraᶜ : IsIncreasingRoutingAlgebra rawAlgebraᶜ
isIncreasingRoutingAlgebraᶜ = record
  { isRoutingAlgebra     = isRoutingAlgebraᶜ
  ; ▷-increasing = ▷ᶜ-increasing
  }

increasingRoutingAlgebraᶜ : IncreasingRoutingAlgebra ℓ₀ (b ⊔ ℓ) ℓ
increasingRoutingAlgebraᶜ = record
  { isIncreasingRoutingAlgebra = isIncreasingRoutingAlgebraᶜ
  }

isStrictlyIncreasingRoutingAlgebraᶜ : IsStrictlyIncreasingRoutingAlgebra rawAlgebraᶜ
isStrictlyIncreasingRoutingAlgebraᶜ = record
  { isRoutingAlgebra     = isRoutingAlgebraᶜ
  ; ▷-strictlyIncreasing = ▷ᶜ-strictlyIncreasing
  }
  
strictlyIncreasingRoutingAlgebraᶜ : StrictlyIncreasingRoutingAlgebra ℓ₀ (b ⊔ ℓ) ℓ
strictlyIncreasingRoutingAlgebraᶜ = record
  { isStrictlyIncreasingRoutingAlgebra = isStrictlyIncreasingRoutingAlgebraᶜ
  }
  
isFiniteStrictlyIncreasingRoutingAlgebraᶜ : IsFiniteStrictlyIncreasingRoutingAlgebra rawAlgebraᶜ
isFiniteStrictlyIncreasingRoutingAlgebraᶜ = record
  { isStrictlyIncreasingRoutingAlgebra = isStrictlyIncreasingRoutingAlgebraᶜ
  ; allRoutes                          = allCRoutes
  ; ∈-allRoutes                        = ∈-allCRoutes
  }

finiteStrictlyIncreasingRoutingAlgebraᶜ : FiniteStrictlyIncreasingRoutingAlgebra ℓ₀ (b ⊔ ℓ) ℓ
finiteStrictlyIncreasingRoutingAlgebraᶜ = record
  { isFiniteStrictlyIncreasingRoutingAlgebra = isFiniteStrictlyIncreasingRoutingAlgebraᶜ
  }
