open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Level using (_⊔_) renaming (zero to ℓ₀)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Properties.PathAlgebra.Consistency as Consistency


module RoutingLib.Routing.Properties.IncreasingPathAlgebra.Consistency
  {a b ℓ n} (algebra : IncreasingPathAlgebra a b ℓ n)
  where

open IncreasingPathAlgebra algebra

------------------------------------------------------------------------------
-- Open increasing path algebra consistency

open Consistency pathAlgebra public

------------------------------------------------------------------------------
-- New properties

▷ᶜ-increasing : ∀ s r → (s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r
▷ᶜ-increasing (i , j) (r , _) = ▷-increasing (A i j) r

------------------------------------------------------------------------------
-- Routing algebra

isIncreasingRoutingAlgebraᶜ : IsIncreasingRoutingAlgebra _≈ᶜ_ _⊕ᶜ_ _▷ᶜ_ C0# C∞
isIncreasingRoutingAlgebraᶜ = record
  { isRoutingAlgebra     = isRoutingAlgebraᶜ
  ; ▷-increasing = ▷ᶜ-increasing
  }

increasingRoutingAlgebraᶜ : IncreasingRoutingAlgebra ℓ₀ (b ⊔ ℓ) ℓ
increasingRoutingAlgebraᶜ = record
  { isIncreasingRoutingAlgebra = isIncreasingRoutingAlgebraᶜ
  }
