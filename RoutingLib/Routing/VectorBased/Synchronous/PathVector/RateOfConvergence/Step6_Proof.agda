open import Data.Fin using (Fin)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_; _^_; _*_; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Unit using ()
open import Data.Product using (proj₁)
open import Function using (_∘_; flip)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)

import RoutingLib.Function.Reasoning as FunctionalReasoning
open import RoutingLib.Routing.Prelude using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step4_InductiveStep as Step4_InductiveStep
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step5_InductiveArgument as Step5_InductiveArgument

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step6_Proof
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (isIncreasing : IsIncreasing algebra)
  (A : AdjacencyMatrix algebra (suc n-1))
  where

open Prelude isRoutingAlgebra isPathAlgebra A

increasing⇒n²-convergence : ∀ X t → σ (n ^ 2 + t) X ≈ₘ σ (n ^ 2) X
increasing⇒n²-convergence X t i j = proj₁ (Cₙ₋₁-conv i) t
  where  
  open Step1_NodeSets          isRoutingAlgebra isPathAlgebra A X j
  open Step2_ConvergedSubtree  isRoutingAlgebra isPathAlgebra isIncreasing A X j using (iₘᵢₙ; iₘᵢₙ∉C)
  open Step4_InductiveStep     isRoutingAlgebra isPathAlgebra isIncreasing A X j using (iₘᵢₙ∈𝓒ₜ₊ₙ)
  open Step5_InductiveArgument isRoutingAlgebra isPathAlgebra A X j iₘᵢₙ iₘᵢₙ∉C n iₘᵢₙ∈𝓒ₜ₊ₙ using (Cₙ₋₁-converged)
 
  n²≡n-1+1+[n-1]*n : n-1 + suc (n-1 * n) ≡ n ^ 2
  n²≡n-1+1+[n-1]*n rewrite *-identityʳ n-1 = +-suc n-1 _

  Cₙ₋₁-conv : ∀ i → i ∈ᵤ 𝓒 (n ^ 2)
  Cₙ₋₁-conv i = begin⟨ Cₙ₋₁-converged i ⟩
    ∴ i ∈ᵤ 𝓒 (suc (n-1 * n))        $⟨ 𝓒ₜ⊆𝓒ₛ₊ₜ (suc (n-1 * n)) n-1 ⟩
    ∴ i ∈ᵤ 𝓒 (n-1 + suc (n-1 * n))  $⟨ flip (𝓒-cong {n-1 + suc (n-1 * n)} {n ^ 2}) n²≡n-1+1+[n-1]*n ⟩
    ∴ i ∈ᵤ 𝓒 (n ^ 2)                ∎
    where open FunctionalReasoning
