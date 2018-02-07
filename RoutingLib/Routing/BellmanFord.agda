open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (foldr; tabulate)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Data.List.All.Properties
  using (foldr-All₂; All₂-tabulate)

module RoutingLib.Routing.BellmanFord
  {a b ℓ n}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 n)
  where
  
  open RoutingProblem 𝓡𝓟

  -- Identity matrix
  I : RMatrix
  I i j with j ≟ᶠ i
  ... | yes _ = 1#
  ... | no  _ = 0#

  -- Algorithm for a single iteration
  σ : RMatrix → RMatrix
  σ X i j = foldr _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

  -- σ respects the underlying matrix equality
  σ-cong : ∀ {X Y} → X ≈ₘ Y → σ X ≈ₘ σ Y
  σ-cong X≈Y i j = foldr-All₂
    _≈_ ⊕-cong ≈-refl (All₂-tabulate (λ k → ▷-cong (A i k) (X≈Y k j)))

  -- A possible parallelisation of the algorithm where each 
  -- node is in charge of its own routes
  σ∥ : Parallelisation (λ _ → ℝ𝕋ₛ)
  σ∥ = record { f = σ }

  open Parallelisation σ∥ using () renaming (async-iter to δ) public
