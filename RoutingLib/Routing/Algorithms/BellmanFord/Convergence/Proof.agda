open import Data.Product using (∃; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_) using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (sym to ≡-sym)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.SufficientConditions
open import RoutingLib.Function.Metric.Contraction using (fixedPoint)

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.Proof where

  module WithoutPaths
    {a b ℓ n-1} 
    (rp : RoutingProblem a b ℓ (suc n-1)) 
    (cc : ConvergenceConditions rp)
    where

    ------------------------------------------------------------------------
    -- Theorem
    --
    -- Distributed Bellman Ford over any RoutingAlgebra converges from 
    -- any state when it is possible to enumerate all values of Route

    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Asynchronous rp
    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Asynchronous.Properties rp

    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.Step1_HeightFunction rp cc using (heightFunction)
    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.Step2_Ultrametric rp cc heightFunction using (d-metric)
    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.Step3_SimilarityIncreasing rp cc heightFunction using (σ-strictlyContractingOnOrbits)
    
    
    abstract
      σ-converges-from-any-state : ∀ X → ∃ λ t → σ^ t X ≈ₘ σ^ (suc t) X
      σ-converges-from-any-state X = fixedPoint d-metric σ _≟ₘ_ σ-strictlyContractingOnOrbits X


  module WithPaths
    {a b ℓ}
    (ra : RoutingAlgebra a b ℓ)
    (ccwp : ConvergenceConditionsWithPaths ra)
    {n-1 : ℕ} 
    (G : Graph (RoutingAlgebra.Step ra) (suc n-1))
    where

    open ConvergenceConditionsWithPaths ccwp
  
    -- Adding consistent paths to the algebra to form a valid routing algebra 
    -- for which we can enumerate all the routes (as there are only a finite number
    -- of paths).
    open import RoutingLib.Routing.AddingSPaths.Consistent ra ⊕-sel one G
    --open import RoutingLib.Routing.AddingSPaths.Consistent.ConvergenceConditionProperties ra G ccwp using () renaming (convergenceConditions to cc)
    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord crp using () renaming (σ^ to σᶜ^; _≈ₘ_ to _≈ᶜₘ_)


    ------------------------------------------------------------------------
    -- Theorem 2
    --
    -- Distributed Bellman Ford converges from any state over any
    -- structure (A,⊕,▷) when consistent paths are added to it 
    -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.

    σ-converges-from-consistent-states : ∀ X → ∃ λ t → σᶜ^ t X ≈ᶜₘ σᶜ^ (suc t) X
    σ-converges-from-consistent-states X = σ-converges-from-any-state X
      where
      open WithoutPaths crp {!!} using (σ-converges-from-any-state) public


{-
    ------------------------------------------------------------------------
    -- Theorem 3
    --
    -- Distributed Bellman Ford converges from any state over any
    -- structure (A,⊕,▷) when paths are added to it 
    -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.

    open import RoutingLib.Routing.AddingPaths.Inconsistent ra ⊕-sel one G using (irp)
    open import RoutingLib.Routing.AddingPaths.Bisimilarity ra ⊕-sel one G using (σ^-≃)
    open import RoutingLib.Routing.AddingPaths.Bisimilarity.Reasoning ra ⊕-sel one G
    open import RoutingLib.Routing.AddingPaths.Bisimilarity.FlushingDBF ra ⊕-sel one G using (i⇨c)

    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord irp
    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties irp
  
    n : ℕ
    n = suc n-1

    σ-converges-from-all-states : ∀ X → ∃ λ t → σ^ t X ≈ₘ σ^ (suc t) X
    σ-converges-from-all-states X with i⇨c X
    ... | Y , Y≃σⁿX with σ-converges-from-consistent-states Y
    ...   | m , σᵐY≈σᵐ⁺¹Y = m + n , λ i j → (
      begin
        σ^ (m + n) X i j
      ≈ⁱ⟨ ≈ₘ-reflexive (σᵐ⁺ⁿ≡σᵐσⁿ m n X) i j ⟩
        σ^ m (σ^ n X) i j
      ≃ᶜⁱ⟨ σ^-≃ m Y≃σⁿX i j ⟩
        σᶜ^ m Y i j
      ≈ᶜ⟨ σᵐY≈σᵐ⁺¹Y i j ⟩
        σᶜ^ (suc m) Y i j
      ≃ⁱᶜ⟨ σ^-≃ (suc m) Y≃σⁿX i j ⟩
        σ^ (suc m) (σ^ n X) i j
      ≈ⁱ⟨ ≈ₘ-reflexive (cong σ (≡-sym (σᵐ⁺ⁿ≡σᵐσⁿ m n X))) i j ⟩
        σ^ (suc (m + n)) X i j
      ∎)

-}
