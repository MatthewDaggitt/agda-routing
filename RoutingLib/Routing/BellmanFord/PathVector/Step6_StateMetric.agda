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
open import RoutingLib.Function.Metric using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq; _StrContrOnOrbitsOver_)
import RoutingLib.Function.Metric.MaxLift as MaxLift
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
    ; isUltrametric to dₜ-isUltrametric
    ) public
  
  dₜ-bounded : Bounded ℝ𝕋ₛ dₜ  
  dₜ-bounded = MaxLift.bounded (λ _ → S) dᵣ dᵣ-bounded
  




  ------------------
  -- State metric --
  ------------------
  
  D-ultrametric : Ultrametric _
  D-ultrametric = MaxLift.ultrametric {n = n} (λ _ → _) (λ _ → dₜ-ultrametric)

  open Ultrametric D-ultrametric public using ()
    renaming
    ( d to D
    ; cong to D-cong
    ; 0⇒eq to D≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒D≡0
    ; sym to D-sym
    )

  D-bounded : Bounded ℝ𝕄ₛ D  
  D-bounded = MaxLift.bounded (λ _ → ℝ𝕋ₛ) dₜ dₜ-bounded



  -- Strictly contracting
  
  D-strContrOrbits : _StrContrOnOrbitsOver_ ℝ𝕄ₛ σ  D
  D-strContrOrbits {X} σX≉X with max[t]∈t 0 (λ i → dₜ (X i) (σ X i))
  ... | inj₁ dXσX≡0              = contradiction (≈ₘ-sym (D≡0⇒X≈Y dXσX≡0)) σX≉X
  ... | inj₂ (r , DXσX≡dₜXᵣσXᵣ) with max[t]∈t 0 (λ i → dᵣ (X r i) (σ X r i))
  ...   | inj₁ dXᵣσXᵣ≡0               = contradiction (≈ₘ-sym (D≡0⇒X≈Y (trans DXσX≡dₜXᵣσXᵣ dXᵣσXᵣ≡0))) σX≉X
  ...   | inj₂ (s , dXᵣσXᵣ≡dᵣXᵣₛσXᵣₛ) = begin
    D (σ X) (σ (σ X))   <⟨ test ⟩
    dᵣ (X r s) (σ X r s) ≡⟨ sym DXσX≈dᵣXᵣₛσXᵣₛ ⟩
    D X (σ X)           ∎
    where
    open ≤-Reasoning

    DXσX≈dᵣXᵣₛσXᵣₛ : D X (σ X) ≡ dᵣ (X r s) (σ X r s)
    DXσX≈dᵣXᵣₛσXᵣₛ = trans DXσX≡dₜXᵣσXᵣ dXᵣσXᵣ≡dᵣXᵣₛσXᵣₛ
    
    Xᵣₛ≉σXᵣₛ : X r s ≉ σ X r s
    Xᵣₛ≉σXᵣₛ Xᵣₛ≈σXᵣₛ = σX≉X (≈ₘ-sym (D≡0⇒X≈Y (trans DXσX≈dᵣXᵣₛσXᵣₛ (x≈y⇒dᵣ≡0 Xᵣₛ≈σXᵣₛ))))

    dᵣ≤dᵣXᵣₛσXᵣₛ : ∀ u v → dᵣ (X u v) (σ X u v) ≤ dᵣ (X r s) (σ X r s)
    dᵣ≤dᵣXᵣₛσXᵣₛ u v = begin
      dᵣ (X u v) (σ X u v) ≤⟨ MaxLift.dᵢ≤d (λ _ → S) dᵣ (X u) (σ X u) v ⟩
      dₜ (X u)   (σ X u)   ≤⟨ MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) dₜ X (σ X) u ⟩
      D X (σ X)           ≡⟨ DXσX≈dᵣXᵣₛσXᵣₛ ⟩
      dᵣ (X r s) (σ X r s) ∎

    0<dᵣXᵣₛσXᵣₛ : 0 < dᵣ (X r s) (σ X r s)
    0<dᵣXᵣₛσXᵣₛ = n≢0⇒0<n (Xᵣₛ≉σXᵣₛ ∘ dᵣ≡0⇒x≈y)
    
    test : D (σ X) (σ (σ X)) < dᵣ (X r s) (σ X r s)
    test = max[t]<x {t = zipWith dₜ (σ X) (σ (σ X))}
             (λ i → max[t]<x {t = zipWith dᵣ (σ X i) (σ (σ X) i)}
               (λ j → dᵣ-strContrOrbits Xᵣₛ≉σXᵣₛ dᵣ≤dᵣXᵣₛσXᵣₛ i j)
               0<dᵣXᵣₛσXᵣₛ)
             0<dᵣXᵣₛσXᵣₛ




  -- Strictly contracting when one of the arguments is consistent
  
  D-strContrᶜ : ∀ {X Y} → 𝑪ₘ X → X ≉ₘ Y → D (σ X) (σ Y) < D X Y
  D-strContrᶜ {X} {Y} Xᶜ X≉Y with max[t]∈t 0 (λ i → dₜ (X i) (Y i))
  ... | inj₁ dXY≡0              = contradiction (D≡0⇒X≈Y dXY≡0) X≉Y
  ... | inj₂ (r , DXY≡dₜXᵣYᵣ) with max[t]∈t 0 (λ i → dᵣ (X r i) (Y r i))
  ...   | inj₁ dXᵣYᵣ≡0               = contradiction (D≡0⇒X≈Y (trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡0)) X≉Y
  ...   | inj₂ (s , dXᵣYᵣ≡dᵣXᵣₛYᵣₛ) = begin
    D  (σ X)   (σ Y)   <⟨ test ⟩
    dᵣ (X r s) (Y r s) ≡⟨ sym DXY≈dᵣXᵣₛYᵣₛ ⟩
    D  X       Y       ∎
    where
    open ≤-Reasoning

    DXY≈dᵣXᵣₛYᵣₛ : D X Y ≡ dᵣ (X r s) (Y r s)
    DXY≈dᵣXᵣₛYᵣₛ = trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡dᵣXᵣₛYᵣₛ
    
    Xᵣₛ≉Yᵣₛ : X r s ≉ Y r s
    Xᵣₛ≉Yᵣₛ Xᵣₛ≈Yᵣₛ = X≉Y (D≡0⇒X≈Y (trans DXY≈dᵣXᵣₛYᵣₛ (x≈y⇒dᵣ≡0 Xᵣₛ≈Yᵣₛ)))

    dᵣ≤dᵣXᵣₛYᵣₛ : ∀ u v → dᵣ (X u v) (Y u v) ≤ dᵣ (X r s) (Y r s)
    dᵣ≤dᵣXᵣₛYᵣₛ u v = begin
      dᵣ (X u v) (Y u v) ≤⟨ MaxLift.dᵢ≤d (λ _ → S) dᵣ (X u) (Y u) v ⟩
      dₜ (X u)   (Y u)   ≤⟨ MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) dₜ X (Y) u ⟩
      D X (Y)           ≡⟨ DXY≈dᵣXᵣₛYᵣₛ ⟩
      dᵣ (X r s) (Y r s) ∎

    0<dᵣXᵣₛYᵣₛ : 0 < dᵣ (X r s) (Y r s)
    0<dᵣXᵣₛYᵣₛ = n≢0⇒0<n (Xᵣₛ≉Yᵣₛ ∘ dᵣ≡0⇒x≈y)
    
    test : D (σ X) (σ Y) < dᵣ (X r s) (Y r s)
    test = max[t]<x {t = zipWith dₜ (σ X) (σ Y)}
             (λ i → max[t]<x {t = zipWith dᵣ (σ X i) (σ Y i)}
               (λ j → dᵣ-strContrᶜ Xᶜ Xᵣₛ≉Yᵣₛ dᵣ≤dᵣXᵣₛYᵣₛ i j)
               0<dᵣXᵣₛYᵣₛ)
             0<dᵣXᵣₛYᵣₛ
  
