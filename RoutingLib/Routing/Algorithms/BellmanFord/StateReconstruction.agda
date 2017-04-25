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
  where

  private

    n : ℕ
    n = suc n-1

  abstract

    open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.Core ra ⊕-sel G
    open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.Activation ra ⊕-sel G
    open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.DataFlow ra ⊕-sel G

    open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G
    open RoutingAlgebra ra using (refl)

    open Schedule
    open import RoutingLib.Routing.Algorithms.BellmanFord crp using (σ∥; I; δ)
    open RoutingProblem crp using (RMatrix)
    open import RoutingLib.Asynchronous.Snapshot σ∥ using (Snapshot; toListⱼ; _≈ₛ_; snapshot)
    open import RoutingLib.Data.List.Any.GenericMembership (Cₛ) using (_∈_)

    open Parallelisation σ∥ using (_≈ₘ_)

    

    -- Schedules
   
{-
    locateTime : ∀ {x xs} → x ∈ xs → 𝕋
    locateTime {_} {xs} (here  _)    = listConstruction𝕋 xs
    locateTime {_} {_}  (there x∈xs) = locateTime x∈xs

    construct𝔹 : ∀ (β : 𝔹 n) tₛ xs → (∀ {t i j} → tₛ ≤ t → β t i j ≤ tₛ → ∃ λ x → x ∈ xs) → 𝔹 n
    construct𝔹 β tₛ xs index t i j with listConstruction𝕋 xs ≤? t | β (tₛ + t ∸ listConstruction𝕋 xs) i j ≤? tₛ
    ... | yes ct≤t | yes β≤tₛ = locateTime (proj₂ (index (subst (tₛ ≤_) (≡-sym (+-∸-assoc tₛ ct≤t)) (m≤m+n tₛ (t ∸ listConstruction𝕋 xs))) β≤tₛ)) 
    ... | _        |  _       = all𝔹 xs t i j
-}

    construction𝕊 : ∀ (𝕤 : Schedule n) t → RMatrix → Snapshot (β 𝕤) t → Schedule n
    construction𝕊 𝕤 t X sn = record
      { α              = final𝔸 𝕤 t X sn
      ; β              = final𝔹 𝕤 t X sn
      ; starvationFree = final𝔸-starvationFree 𝕤 t X sn
      ; causal         = final𝔹-causal 𝕤 t X sn
      ; dynamic        = final𝔹-dynamic 𝕤 t X sn
      }

    δᵗ¹X≈δᶜᵗI : ∀ 𝕤 t X (sn : Snapshot (β 𝕤) t) → X ≈ₘ δ (construction𝕊 𝕤 t X sn) (build𝕋 X (dynamic 𝕤) sn) I
    δᵗ¹X≈δᶜᵗI 𝕤 t X sn = {!!}

    𝕤₁≈c𝕤 : ∀ 𝕤 tₛ X (sn : Snapshot (β 𝕤) tₛ) →  𝕤 ⟦ tₛ ⟧≈⟦ build𝕋 X (dynamic 𝕤) sn ⟧ construction𝕊 𝕤 tₛ X sn
    𝕤₁≈c𝕤 𝕤 tₛ X sn = final𝔸-≈𝔸 𝕤 tₛ X sn , {!final𝔹-≈𝔹 𝕤 tₛ X sn!} 
    
    sn₁≈csn : ∀ 𝕤 t X (sn : Snapshot (β 𝕤) t) → sn ≈ₛ snapshot (construction𝕊 𝕤 t X sn) (build𝕋 X (dynamic 𝕤) sn) I
    sn₁≈csn 𝕤 t X sn = {!!}


    reconstructionAll : ∀ 𝕤₁ t₁ X (sn₁ : Snapshot (β 𝕤₁) t₁) → ∃₂ λ 𝕤₂ t₂ → X ≈ₘ δ 𝕤₂ t₂ I × 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ × sn₁ ≈ₛ snapshot 𝕤₂ t₂ I
    reconstructionAll 𝕤₁ t₁ X sn₁ = construction𝕊 𝕤₁ t₁ X sn₁ , build𝕋 X (dynamic 𝕤₁) sn₁ , δᵗ¹X≈δᶜᵗI 𝕤₁ t₁ X sn₁ , 𝕤₁≈c𝕤 𝕤₁ t₁ X sn₁ , sn₁≈csn 𝕤₁ t₁ X sn₁
      where open Schedule 𝕤₁
