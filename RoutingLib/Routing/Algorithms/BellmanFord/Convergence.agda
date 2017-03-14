open import Data.Product using (∃; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_; s≤s; _<_; _≤_; _≤?_; _∸_)
open import Data.Nat.Properties using (m≤m+n; m+n∸m≡n)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Function.HeightFunction using (BoundedHeightFunction)
open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.SufficientConditions
open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Theorems using (module Guerney)
open import RoutingLib.Data.Nat.Properties using (suc-injective; m≤n⇨m+o≡n; ≰⇒≥; +-comm; +-assoc)

module RoutingLib.Routing.Algorithms.BellmanFord.Convergence where

  module WithoutPaths
    {a b ℓ n-1} 
    (rp : RoutingProblem a b ℓ (suc n-1)) 
    (cc : ConvergenceConditions (RoutingProblem.ra rp))
    where

    open RoutingProblem rp

    ------------------------------------------------------------------------
    -- Theorem
    --
    -- Distributed Bellman Ford over any RoutingAlgebra converges from 
    -- any state when it is possible to enumerate all values of Route

    open import RoutingLib.Routing.Algorithms.BellmanFord rp
    --open import RoutingLib.Routing.Algorithms.BellmanFord.Asynchronous.Properties rp

    open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.Step1_HeightFunction rp cc using (heightFunction; height)
    open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.Step2_Ultrametric rp cc heightFunction using (d; d-isUltrametric; d≤H)
    open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.Step3_SimilarityIncreasing rp cc heightFunction using (σ-strictlyContractingOnOrbits)
    open BoundedHeightFunction heightFunction using (hₘₐₓ)

    d-satisfiesUltrametricConditions : Guerney.UltrametricConditions σ∥ d
    d-satisfiesUltrametricConditions = record
      { isUltrametric               = {!!} --d-isUltrametric
      ; strictlyContractingOnOrbits = σ-strictlyContractingOnOrbits
      ; finiteImage                 = suc hₘₐₓ , d≤H
      }

    σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
    σ-isAsynchronouslySafe = Guerney.StrictlyContractingUltrametric⇒AsynchronouslySafe σ∥ (d , d-satisfiesUltrametricConditions)









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
    open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G
    open import RoutingLib.Routing.AlgebraicPaths.Consistent.Properties ra ⊕-sel G using (convergenceConditions)
    open import RoutingLib.Routing.Algorithms.BellmanFord crp using () renaming (I to Iᶜ; σ∥ to σ∥ᶜ)


    ------------------------------------------------------------------------
    -- Theorem 2
    --
    -- Distributed Bellman Ford converges from any state over any
    -- structure (A,⊕,▷,0,1) when consistent paths are added to it 
    -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.

    σᶜ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥ᶜ
    σᶜ-isAsynchronouslySafe = σ-isAsynchronouslySafe
      where
      open WithoutPaths crp (convergenceConditions ccwp) using (σ-isAsynchronouslySafe)




    ------------------------------------------------------------------------
    -- Theorem 3
    --
    -- Distributed Bellman Ford converges from any state over any
    -- structure (A,⊕,▷,0,1) when paths are added to it 
    -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.

    open import RoutingLib.Routing.AlgebraicPaths.Inconsistent ra ⊕-sel G using (IRoute; irp; ≈ⁱ-reflexive)


    open import RoutingLib.Routing.AlgebraicPaths.Bisimilarity ra ⊕-sel G using (module InconsistentReasoning; toIRoute-≃)
    open InconsistentReasoning

    open import RoutingLib.Routing.Algorithms.BellmanFord.AddingPaths ra ⊕-sel G using (convergeToConsistency; δ-≃; ≃ₛ⇒≃ₘ)
    open import RoutingLib.Routing.Algorithms.BellmanFord irp using () renaming (σ∥ to σ∥ⁱ)
    
    open Parallelisation σ∥ᶜ using () renaming (δ to δᶜ)
    open Parallelisation σ∥ⁱ using (_≈ₘ_) renaming (δ to δⁱ)

    open IsAsynchronouslySafe σᶜ-isAsynchronouslySafe renaming
      ( m* to m*ᶜ
      ; m*-reached to m*-reachedᶜ
      )

    m*ⁱ : Fin (suc n-1) → Fin (suc n-1) → IRoute
    m*ⁱ i j = toIRoute (m*ᶜ i j)

    tⁱᶠ : ∀ 𝕤 X → ℕ
    tⁱᶠ 𝕤 X with convergeToConsistency 𝕤 X
    ... | (tᶜ , tʳ , 𝕤ʳ , δᵗᶜX≃δᵗʳI , 𝕤≈𝕤ʳ , snᵗᶜ≈snᵗʳ) with m*-reachedᶜ 𝕤ʳ Iᶜ 
    ...   | (tᶜᶠ , _) with tʳ ≤? tᶜᶠ
    ...     | yes _ = tᶜ + (tᶜᶠ ∸ tʳ)
    ...     | no  _ = tᶜ

    m*-reachedⁱ : ∀ 𝕤 X t → δⁱ 𝕤 (tⁱᶠ 𝕤 X + t) X ≈ₘ m*ⁱ
    m*-reachedⁱ 𝕤 X t i j with convergeToConsistency 𝕤 X
    ... | (tᶜ , tʳ , 𝕤ʳ , δᵗᶜX≃δᵗʳI , 𝕤≈𝕤ʳ , snᵗᶜ≃snᵗʳ) with m*-reachedᶜ 𝕤ʳ Iᶜ 
    ...   | (tᶜᶠ , δᵗᶜᶠI≈m*ᶜ) with tʳ ≤? tᶜᶠ 
    ...     | yes tʳ≤tᶜᶠ = 
      begin
        δⁱ 𝕤 (tᶜ + (tᶜᶠ ∸ tʳ) + t)   X i j  ≈ⁱ⟨ ≈ⁱ-reflexive (cong (λ t' → δⁱ 𝕤 t' X i j) (+-assoc tᶜ (tᶜᶠ ∸ tʳ) t)) ⟩
        δⁱ 𝕤 (tᶜ + ((tᶜᶠ ∸ tʳ) + t)) X i j  ≈ⁱ⟨ ≈ⁱ-reflexive (cong (λ t' → δⁱ 𝕤 t' X i j) (+-comm tᶜ _)) ⟩
        δⁱ 𝕤 (tᶜᶠ ∸ tʳ + t + tᶜ)     X i j  ≃ⁱᶜ⟨ ≃ₛ⇒≃ₘ X Iᶜ 𝕤≈𝕤ʳ snᵗᶜ≃snᵗʳ δᵗᶜX≃δᵗʳI ((tᶜᶠ ∸ tʳ) + t) i j ⟩
        δᶜ 𝕤ʳ (tᶜᶠ ∸ tʳ + t + tʳ)     Iᶜ i j  ≈ᶜ⟨ ≈ᶜ-reflexive (cong (λ t' → δᶜ 𝕤ʳ t' Iᶜ i j) (+-comm _ tʳ)) ⟩
        δᶜ 𝕤ʳ (tʳ + (tᶜᶠ ∸ tʳ + t))   Iᶜ i j  ≈ᶜ⟨ ≈ᶜ-reflexive (cong (λ t' → δᶜ 𝕤ʳ t' Iᶜ i j) (≡-sym (+-assoc tʳ (tᶜᶠ ∸ tʳ) t))) ⟩
        δᶜ 𝕤ʳ (tʳ + (tᶜᶠ ∸ tʳ) + t)   Iᶜ i j  ≈ᶜ⟨ ≈ᶜ-reflexive (cong (λ t' → δᶜ 𝕤ʳ (t' + t) Iᶜ i j) (m+n∸m≡n tʳ≤tᶜᶠ)) ⟩
        δᶜ 𝕤ʳ (tᶜᶠ + t)              Iᶜ i j  ≈ᶜ⟨ δᵗᶜᶠI≈m*ᶜ t i j ⟩
        m*ᶜ i j                            ≃ᶜⁱ⟨ toIRoute-≃ (m*ᶜ i j) ⟩
        m*ⁱ i j
      ∎
    ...     | no tʳ≰tᶜᶠ with m≤n⇨m+o≡n (≰⇒≥ tʳ≰tᶜᶠ)
    ...       | (t' , tᶜᶠ+t'≡tʳ) =
      begin
        δⁱ 𝕤 (tᶜ + t)         X i j  ≈ⁱ⟨ ≈ⁱ-reflexive (cong (λ t' → δⁱ 𝕤 t' X i j) (+-comm tᶜ _)) ⟩
        δⁱ 𝕤 (t + tᶜ)         X i j  ≃ⁱᶜ⟨ ≃ₛ⇒≃ₘ X Iᶜ 𝕤≈𝕤ʳ snᵗᶜ≃snᵗʳ δᵗᶜX≃δᵗʳI t i j ⟩
        δᶜ 𝕤ʳ (t + tʳ)         Iᶜ i j  ≈ᶜ⟨ ≈ᶜ-reflexive (cong (λ t' → δᶜ 𝕤ʳ t' Iᶜ i j) (+-comm _ tʳ)) ⟩
        δᶜ 𝕤ʳ (tʳ + t)         Iᶜ i j  ≈ᶜ⟨ ≈ᶜ-reflexive (cong (λ t' → δᶜ 𝕤ʳ (t' + t) Iᶜ i j) (≡-sym tᶜᶠ+t'≡tʳ)) ⟩
        δᶜ 𝕤ʳ (tᶜᶠ + t' + t)   Iᶜ i j  ≈ᶜ⟨ ≈ᶜ-reflexive (cong (λ t' → δᶜ 𝕤ʳ t' Iᶜ i j) (+-assoc tᶜᶠ _ _)) ⟩
        δᶜ 𝕤ʳ (tᶜᶠ + (t' + t)) Iᶜ i j  ≈ᶜ⟨ δᵗᶜᶠI≈m*ᶜ (t' + t) i j ⟩
        m*ᶜ i j                      ≃ᶜⁱ⟨ toIRoute-≃ (m*ᶜ i j) ⟩
        m*ⁱ i j
      ∎

    σⁱ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥ⁱ
    σⁱ-isAsynchronouslySafe = record 
      { m*         = m*ⁱ 
      ; m*-reached = λ 𝕤 X → tⁱᶠ 𝕤 X , m*-reachedⁱ 𝕤 X
      }
