open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂; cong₂)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Data.Nat.Properties using (m<n⇒n≢0; n≢0⇒0<n; n≤0⇒n≡0; module ≤-Reasoning)
open import RoutingLib.Data.Table using (Table; zipWith; max)
open import RoutingLib.Data.Table.Properties using (max[t]<x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Function.Metric as Metric using (IsUltrametric; Bounded)
import RoutingLib.Function.Metric.MaxLift as MaxLift

import RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Step4_RouteMetric as Step4

module RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Step5_StateMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step4 𝓟𝓢𝓒

  ------------------
  -- Table metric --
  ------------------

  dₜ : RTable → RTable → ℕ
  dₜ x y = max 0 (zipWith dᵣ x y)
  
  dₜ-isUltrametric : IsUltrametric _ dₜ
  dₜ-isUltrametric = MaxLift.isUltrametric {n = n} (λ _ → S) dᵣ-isUltrametric

  dₜ-bounded : Bounded ℝ𝕋ₛ dₜ  
  dₜ-bounded = MaxLift.bounded (λ _ → S) dᵣ-bounded

  ------------------
  -- State metric --
  ------------------

  D : RMatrix → RMatrix → ℕ
  D X Y = max 0 (zipWith dₜ X Y)
  
  D-isUltrametric : IsUltrametric _ D
  D-isUltrametric = MaxLift.isUltrametric {n = n} (λ _ → _) dₜ-isUltrametric

  D-bounded : Bounded ℝ𝕄ₛ D  
  D-bounded = MaxLift.bounded (λ _ → ℝ𝕋ₛ) dₜ-bounded

  open IsUltrametric D-isUltrametric public using ()
    renaming
    ( cong to D-cong
    ; 0⇒eq to D≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒D≡0
    ; sym to D-sym
    )

  -- Strictly contracting

  open Metric ℝ𝕄ₛ using (_StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)
  
  σ-strContrOrbits : σ StrContrOnOrbitsOver D
  σ-strContrOrbits {X} σX≉X with max[t]∈t 0 (λ i → dₜ (X i) (σ X i))
  ... | inj₁ dXσX≡0              = contradiction (≈ₘ-sym (D≡0⇒X≈Y dXσX≡0)) σX≉X
  ... | inj₂ (r , DXσX≡dₜXᵣσXᵣ) with max[t]∈t 0 (λ i → dᵣ (X r i) (σ X r i))
  ...   | inj₁ dXᵣσXᵣ≡0               = contradiction (≈ₘ-sym (D≡0⇒X≈Y (trans DXσX≡dₜXᵣσXᵣ dXᵣσXᵣ≡0))) σX≉X
  ...   | inj₂ (s , dXᵣσXᵣ≡dᵣXᵣₛσXᵣₛ) = begin
    D (σ X) (σ (σ X))   <⟨ test ⟩
    dᵣ (X r s) (σ X r s) ≡⟨ sym DXσX≈dᵣXᵣₛσXᵣₛ ⟩
    D X (σ X)            ∎
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
  
  σ-strContrᶜ : ∀ {X Y} → 𝑪ₘ X → X ≉ₘ Y → D (σ X) (σ Y) < D X Y
  σ-strContrᶜ {X} {Y} Xᶜ X≉Y with max[t]∈t 0 (λ i → dₜ (X i) (Y i))
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
  
  σ-strContrOnFP : σ StrContrOnFixedPointOver D
  σ-strContrOnFP {X} {X*} σX*≈X* X≉X* = begin
    D X*     (σ X) ≡⟨ D-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σ X}) ⟩
    D (σ X*) (σ X) <⟨ σ-strContrᶜ (fixedᶜ σX*≈X*) (X≉X* ∘ ≈ₘ-sym) ⟩
    D X*     X     ∎
    where open ≤-Reasoning
