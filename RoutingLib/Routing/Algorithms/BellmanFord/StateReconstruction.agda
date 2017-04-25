open import Algebra.FunctionProperties using (Selective)
open import Data.List.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; sum; map; foldr; concat)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _≤?_; z≤n; s≤s; module ≤-Reasoning; ≤-pred)
open import Data.Nat.Properties using (_+-mono_; n∸n≡0; +-∸-assoc; ∸-+-assoc; ≤-step; n≤m+n; m≤m+n; ≰⇒>)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; +-assoc; +-comm)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset using (⁅_⁆; ⊤)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Relation.Binary using (tri<; tri>; tri≈)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; module ≡-Reasoning; inspect; [_]; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∷_∣_; _∺_∣_; source; destination; edge-∷)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty using (SimplePathⁿᵗ; length)
open import RoutingLib.Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; cmp; m∸n≡0⇒m≤n; m≤n⇒m∸n≡0; m<n⇒n∸m≡1+o; <⇒≤)
open import RoutingLib.Routing.Definitions using (RoutingAlgebra; RoutingProblem)
open import RoutingLib.Data.List using (tabulate)

module RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction
  {a b ℓ n-1} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (G : Graph (RoutingAlgebra.Step ra) (suc n-1))
  (𝕤 : Schedule (suc n-1))
  where

  private

    n : ℕ
    n = suc n-1

  abstract

    open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.Core ra ⊕-sel G
    open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.Activation ra ⊕-sel G
    open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.DataFlow ra ⊕-sel G
    open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G

    open import RoutingLib.Routing.Algorithms.BellmanFord crp using (σ∥; I; δ)
    open import RoutingLib.Asynchronous.Snapshot σ∥ using (Snapshot; _≈ₛ_; snapshot)
    open RoutingProblem crp using (RMatrix)
    open Parallelisation σ∥ using (_≈ₘ_)
    open Schedule 𝕤


    -- The final reconstructed schedule
    𝕤ʳ : ∀ {tₛ} → RMatrix → Snapshot β tₛ → Schedule n
    𝕤ʳ {tₛ} X sn = record
      { α              = final𝔸 𝕤 tₛ X sn
      ; β              = final𝔹 𝕤 tₛ X sn
      ; starvationFree = final𝔸-starvationFree 𝕤 tₛ X sn
      ; causal         = final𝔹-causal 𝕤 tₛ X sn
      ; dynamic        = final𝔹-dynamic 𝕤 tₛ X sn
      }

    -- We need to show that when the new schedule 𝕤ʳ merges that the state (δ 𝕤ʳ build𝕋 I) matches up with the provided state (X)
    postulate X≈δᵗʳI : ∀ X {tₛ} (sn : Snapshot β tₛ) → X ≈ₘ δ (𝕤ʳ X sn) (build𝕋 X dynamic sn) I

    -- After merging, the reconstructed schedule 𝕤ʳ must be equal to the original schedule 𝕤
    postulate 𝕤≈𝕤ʳ : ∀ X {tₛ} (sn : Snapshot β tₛ) →  𝕤 ⟦ tₛ ⟧≈⟦ build𝕋 X dynamic sn ⟧ 𝕤ʳ X sn
    
    -- We also need to show that the messages in flight at the merge time are the same for both schedules
    postulate sn≈snʳ : ∀ X {tₛ} (sn : Snapshot β tₛ) → sn ≈ₛ snapshot (𝕤ʳ X sn) (build𝕋 X dynamic sn) I


    reconstructionAll : ∀ X {tₛ} (sn : Snapshot β tₛ) → 
                          ∃₂ λ 𝕤ʳ tʳ → 
                            X ≈ₘ δ 𝕤ʳ tʳ I × 
                            𝕤 ⟦ tₛ ⟧≈⟦ tʳ ⟧ 𝕤ʳ × 
                            sn ≈ₛ snapshot 𝕤ʳ tʳ I
    reconstructionAll X sn = 𝕤ʳ X sn , build𝕋 X dynamic sn , X≈δᵗʳI X sn , 𝕤≈𝕤ʳ X sn , sn≈snʳ X sn
