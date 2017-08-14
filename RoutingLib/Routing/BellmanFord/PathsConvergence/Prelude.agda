open import Algebra.FunctionProperties using (Selective)
open import Data.Nat using (ℕ)

open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathsConvergence.SufficientConditions
import RoutingLib.Routing.AlgebraicPaths.Consistent as ConsistentPaths
import RoutingLib.Routing.AlgebraicPaths.Inconsistent as InconsistentPaths
import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.BellmanFord.PathsConvergence.Prelude
  {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ 𝓡𝓐) (RoutingAlgebra._⊕_ 𝓡𝓐))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) n)
  where

  open ConsistentPaths   𝓡𝓐 ⊕-sel G public renaming (size to sizeᶜ)
  open InconsistentPaths 𝓡𝓐 ⊕-sel G public renaming (size to sizeⁱ) hiding (weight; ⊕-select; sel₁; sel₂; sel≈)
  
  open RoutingAlgebra 𝓡𝓐 public
  open RoutingProblem 𝓡𝓟ᶜ public using () renaming
    ( ℝ𝕄ₛ     to ℝ𝕄ᶜₛ
    ; RMatrix  to CMatrix
    ; _≈ₘ_     to _≈ᶜₘ_
    ; _≉ₘ_     to _≉ᶜₘ_
    ; ≈ₘ-refl  to ≈ᶜₘ-refl
    ; ≈ₘ-sym   to ≈ᶜₘ-sym
    ; ≈ₘ-trans to ≈ᶜₘ-trans
    )
  open RoutingProblem 𝓡𝓟ⁱ public using () renaming
    ( ℝ𝕄ₛ     to ℝ𝕄ⁱₛ
    ; RMatrix  to IMatrix
    ; _≈ₘ_     to _≈ⁱₘ_
    ; _≉ₘ_     to _≉ⁱₘ_
    ; _≟ₘ_     to _≟ⁱₘ_
    ; ≈ₘ-refl  to ≈ⁱₘ-refl
    ; ≈ₘ-sym   to ≈ⁱₘ-sym
    ; ≈ₘ-trans to ≈ⁱₘ-trans
    )
  
  open BellmanFord 𝓡𝓟ⁱ public using () renaming (σ to σⁱ; σ-cong to σⁱ-cong; I to Iⁱ)
  open BellmanFord 𝓡𝓟ᶜ public using () renaming (σ to σᶜ; σ-cong to σᶜ-cong; I to Iᶜ)

  
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent.Properties 𝓡𝓐 ⊕-sel G public renaming
    ( size<n to sizeⁱ<n
    )
    
  open import RoutingLib.Routing.AlgebraicPaths.Consistent.Properties 𝓡𝓐 ⊕-sel G public
  
  open import RoutingLib.Routing.AlgebraicPaths.Translation 𝓡𝓐 ⊕-sel G public
