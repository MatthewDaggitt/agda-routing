open import Data.Product using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m+n∸m≡n; +-mono-≤; ∸-mono;  ⊓-mono-<; m≤m⊔n; m⊓n≤m; ≰⇒≥)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; cong₂)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using () renaming (SufficientConditions to GeneralSufficientConditions)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m; m<n⇒n≢0; ≤-stepsʳ; +-monoʳ-≤; +-monoʳ-<; n≢0⇒0<n; n≤0⇒n≡0; module ≤-Reasoning)
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])
open import RoutingLib.Data.Table using (Table; zipWith)
open import RoutingLib.Data.Table.Properties using (max[t]<x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Function.Distance using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq; _StrContrOnOrbitsOver_)
import RoutingLib.Function.Distance.MaxLift as MaxLift
open import RoutingLib.Function.Image using (FiniteImage)

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step4_RouteMetric as Step4

module RoutingLib.Routing.BellmanFord.PathVector.Step6_StateMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step4 𝓟𝓢𝓒

  ------------------
  -- Table metric --
  ------------------

  dₜ-ultrametric : Ultrametric _
  dₜ-ultrametric = MaxLift.ultrametric {n = n} (λ _ → S) (λ _ → dᵣ-ultrametric)

  open Ultrametric dₜ-ultrametric using () renaming
    ( d       to dₜ
    ; eq⇒0 to x≈y⇒dₜ≡0
    )
  
  dₜ-bounded : Bounded ℝ𝕋ₛ dₜ  
  dₜ-bounded = MaxLift.bounded (λ _ → S) dᵣ dᵣ-bounded
  




  ------------------
  -- State metric --
  ------------------
  
  dₛ-ultrametric : Ultrametric _
  dₛ-ultrametric = MaxLift.ultrametric {n = n} (λ _ → _) (λ _ → dₜ-ultrametric)

  open Ultrametric dₛ-ultrametric public using ()
    renaming
    ( d to dₛ
    ; 0⇒eq to dₛ≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒dₛ≡0
    ; sym to dₛ-sym
    )

  dₛ-bounded : Bounded ℝ𝕄ₛ dₛ  
  dₛ-bounded = MaxLift.bounded (λ _ → ℝ𝕋ₛ) dₜ dₜ-bounded



  -- Strictly contracting
  
  dₛ-eqStrContracting : ∀ {X Y} → Y ≉ₘ X → dₛ (σ X) (σ Y) ≡ 0 → dₛ (σ X) (σ Y) < dₛ X Y
  dₛ-eqStrContracting {X} {Y} Y≉X d[σX,σY]≡0 = begin
    dₛ (σ X) (σ Y) ≡⟨ d[σX,σY]≡0 ⟩
    0              <⟨ n≢0⇒0<n (Y≉X ∘ ≈ₘ-sym ∘ dₛ≡0⇒X≈Y) ⟩
    dₛ X Y         ∎
    where open ≤-Reasoning
    
  dₘ-strContrOrbits : _StrContrOnOrbitsOver_ ℝ𝕄ₛ σ  dₛ
  dₘ-strContrOrbits {X} σX≉X with max[t]∈t 0 (λ i → dₜ (X i) (σ X i))
  ... | inj₁ dXσX≡0              = contradiction (≈ₘ-sym (dₛ≡0⇒X≈Y dXσX≡0)) σX≉X
  ... | inj₂ (r , dₛXσX≡dₜXᵣσXᵣ) with max[t]∈t 0 (λ i → dᵣ (X r i) (σ X r i))
  ...   | inj₁ dXᵣσXᵣ≡0               = contradiction (≈ₘ-sym (dₛ≡0⇒X≈Y (trans dₛXσX≡dₜXᵣσXᵣ dXᵣσXᵣ≡0))) σX≉X
  ...   | inj₂ (s , dXᵣσXᵣ≡dᵣXᵣₛσXᵣₛ) = begin
    dₛ (σ X) (σ (σ X))   <⟨ test ⟩
    dᵣ (X r s) (σ X r s) ≡⟨ sym dₛXσX≈dᵣXᵣₛσXᵣₛ ⟩
    dₛ X (σ X)           ∎
    where
    open ≤-Reasoning

    dₛXσX≈dᵣXᵣₛσXᵣₛ : dₛ X (σ X) ≡ dᵣ (X r s) (σ X r s)
    dₛXσX≈dᵣXᵣₛσXᵣₛ = trans dₛXσX≡dₜXᵣσXᵣ dXᵣσXᵣ≡dᵣXᵣₛσXᵣₛ
    
    Xᵣₛ≉σXᵣₛ : X r s ≉ σ X r s
    Xᵣₛ≉σXᵣₛ Xᵣₛ≈σXᵣₛ = σX≉X (≈ₘ-sym (dₛ≡0⇒X≈Y (trans dₛXσX≈dᵣXᵣₛσXᵣₛ (x≈y⇒dᵣ≡0 Xᵣₛ≈σXᵣₛ))))

    dᵣ≤dᵣXᵣₛσXᵣₛ : ∀ u v → dᵣ (X u v) (σ X u v) ≤ dᵣ (X r s) (σ X r s)
    dᵣ≤dᵣXᵣₛσXᵣₛ u v = begin
      dᵣ (X u v) (σ X u v) ≤⟨ MaxLift.dᵢ≤d (λ _ → S) dᵣ (X u) (σ X u) v ⟩
      dₜ (X u)   (σ X u)   ≤⟨ MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) dₜ X (σ X) u ⟩
      dₛ X (σ X)           ≡⟨ dₛXσX≈dᵣXᵣₛσXᵣₛ ⟩
      dᵣ (X r s) (σ X r s) ∎

    0<dᵣXᵣₛσXᵣₛ : 0 < dᵣ (X r s) (σ X r s)
    0<dᵣXᵣₛσXᵣₛ = n≢0⇒0<n (Xᵣₛ≉σXᵣₛ ∘ dᵣ≡0⇒x≈y)
    
    test : dₛ (σ X) (σ (σ X)) < dᵣ (X r s) (σ X r s)
    test = max[t]<x {t = zipWith dₜ (σ X) (σ (σ X))}
             (λ i → max[t]<x {t = zipWith dᵣ (σ X i) (σ (σ X) i)}
               (λ j → dᵣ-strContrOrbits Xᵣₛ≉σXᵣₛ dᵣ≤dᵣXᵣₛσXᵣₛ i j)
               0<dᵣXᵣₛσXᵣₛ)
             0<dᵣXᵣₛσXᵣₛ
