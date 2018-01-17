open import Data.Product using (∃; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_)
open import Data.Nat.Properties using (m≤m+n; m+n∸m≡n)
open import Data.Fin using (Fin)
open import Data.List using (List; map; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions using (PathSufficientConditions)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using () renaming (SufficientConditions to GeneralSufficientConditions)
open import RoutingLib.Asynchronous
open import RoutingLib.Data.List using (max)

module RoutingLib.Routing.BellmanFord.PathVector
  {a b ℓ}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (sc : PathSufficientConditions 𝓡𝓐)
  {n-1 : ℕ} 
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) (suc n-1))
  where

  private
    n : ℕ
    n = suc n-1

  ------------------------------------------------------------------------
  -- Theorem 2
  --
  -- Distributed Bellman Ford converges from any state over any
  -- structure (A,⊕,▷,0,1) when consistent paths are added to it 
  -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.

  open PathSufficientConditions sc
  open import RoutingLib.Routing.AlgebraicPaths.Consistent 𝓡𝓐 ⊕-sel G using (𝓡𝓟ᶜ; 𝓡𝓐ᶜ)
  open import RoutingLib.Routing.AlgebraicPaths.Consistent.Properties 𝓡𝓐 ⊕-sel G using (convertSufficientConditions)
  open import RoutingLib.Routing.BellmanFord 𝓡𝓟ᶜ  using () renaming (I to Iᶜ; σ∥ to σ∥ᶜ)
  
  generalSufficientConditionsᶜ : GeneralSufficientConditions 𝓡𝓐ᶜ
  generalSufficientConditionsᶜ = convertSufficientConditions sc

  σᶜ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥ᶜ
  σᶜ-isAsynchronouslySafe = σ-isAsynchronouslySafe 𝓡𝓟ᶜ generalSufficientConditionsᶜ
    where open import RoutingLib.Routing.BellmanFord.GeneralConvergence using (σ-isAsynchronouslySafe)




  ------------------------------------------------------------------------
  -- Theorem 3
  --
  -- Distributed Bellman Ford converges from any state over any
  -- structure (A,⊕,▷,0,1) when paths are added to it 
  -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.

  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent 𝓡𝓐 ⊕-sel G using (𝓡𝓟ⁱ)
  open import RoutingLib.Routing.BellmanFord 𝓡𝓟ⁱ using () renaming (σ to σⁱ; σ∥ to σ∥ⁱ)
  
  σⁱ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥ⁱ
  σⁱ-isAsynchronouslySafe = {!!}
