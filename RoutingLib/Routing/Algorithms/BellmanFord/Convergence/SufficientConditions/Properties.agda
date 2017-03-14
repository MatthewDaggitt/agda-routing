open import Data.Product using (∃)
open import Data.Sum using (_⊎_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.SufficientConditions

module RoutingLib.Routing.Algorithms.BellmanFord.Convergence.SufficientConditions.Properties
  {a b ℓ n}
  (rp : RoutingProblem a b ℓ n)
  (cc : ConvergenceConditions (RoutingProblem.ra rp)) where
  
  open RoutingProblem rp
  open ConvergenceConditions cc

  open import RoutingLib.Routing.Algorithms.BellmanFord rp
  import RoutingLib.Routing.Algorithms.BellmanFord.Properties rp as P

  -- A route is always either an extension of an existing route or the identity matrix
  σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
  σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ = P.σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel

  -- Under the following assumptions about ⊕, A▷ₘ always chooses the "best" option with respect to ⊕
  σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : ∀ X i j k → σ X i j ≤ A i k ▷ X k j
  σXᵢⱼ≤Aᵢₖ▷Xₖⱼ = P.σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-sel ⊕-comm ⊕-assoc

  -- After an iteration, the diagonal of the RMatrix is always the identity
  σXᵢᵢ≈Iᵢᵢ : ∀ X i → σ X i i ≈ I i i
  σXᵢᵢ≈Iᵢᵢ = P.σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕

  -- After an iteration, the diagonals of any two RMatrices are equal
  σXᵢᵢ≈σYᵢᵢ : ∀ X Y i → σ X i i ≈ σ Y i i
  σXᵢᵢ≈σYᵢᵢ = P.σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕
