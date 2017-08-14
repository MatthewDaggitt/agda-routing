open import Data.Product using (∃)
open import Data.Sum using (_⊎_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions

module RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions.Properties
  {a b ℓ n}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 n) 
  (sc : SufficientConditions 𝓡𝓐)
  where

  open RoutingProblem 𝓡𝓟
  open SufficientConditions sc

  open import RoutingLib.Routing.BellmanFord 𝓡𝓟
  import RoutingLib.Routing.BellmanFord.Properties 𝓡𝓟 as P

  -- A route is always either an extension of an existing route or the identity matrix
  σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
  σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ = P.σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel

  -- A▷ₘ always chooses the "best" option with respect to ⊕
  σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : ∀ X i j k → σ X i j ≤ A i k ▷ X k j
  σXᵢⱼ≤Aᵢₖ▷Xₖⱼ = P.σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-idem ⊕-assoc ⊕-comm

  -- After an iteration, the diagonal of the RMatrix is always the identity
  σXᵢᵢ≈Iᵢᵢ : ∀ X i → σ X i i ≈ I i i
  σXᵢᵢ≈Iᵢᵢ = P.σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕

  -- After an iteration, the diagonals of any two RMatrices are equal
  σXᵢᵢ≈σYᵢᵢ : ∀ X Y i → σ X i i ≈ σ Y i i
  σXᵢᵢ≈σYᵢᵢ = P.σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕
