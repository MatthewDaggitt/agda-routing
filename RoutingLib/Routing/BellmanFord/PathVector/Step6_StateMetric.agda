open import Data.Product using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m+n∸m≡n; +-mono-≤; ∸-mono;  ⊓-mono-<; m≤m⊔n; m⊓n≤m; ≰⇒≥; n≤m⊔n; m⊓n≤n; <-transˡ; <-transʳ; +-distribˡ-⊔)
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
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Function.Distance using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)
import RoutingLib.Function.Distance.MaxLift as MaxLift
open import RoutingLib.Function.Image using (FiniteImage)

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Preludeᶜ
--import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_Ultrametric as Step2ᶜ
import RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StateMetric as Step3ᶜ
import RoutingLib.Routing.BellmanFord.PathVector.Step5_TableMetric as Step5

module RoutingLib.Routing.BellmanFord.PathVector.Step6_StateMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step5 𝓟𝓢𝓒

  ------------
  -- Metric --
  ------------
  
  open import RoutingLib.Function.Distance ℝ𝕄ₛ using (_StrContrOver_)

  dₘ-ultrametric : Ultrametric _
  dₘ-ultrametric = MaxLift.ultrametric {n = n} (λ _ → _) (λ _ → dₜ-ultrametric)

  open Ultrametric dₘ-ultrametric public using ()
    renaming
    ( d to dₘ
    ; 0⇒eq to dₘ≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒dₘ≡0
    ; sym to dₘ-sym
    )


  dₘ-bounded : Bounded ℝ𝕄ₛ dₘ  
  dₘ-bounded = MaxLift.bounded (λ _ → ℝ𝕋ₛ) dₜ dₜ-bounded

  -- Strictly contracting
  
  dₘ-eqStrContracting : ∀ {X Y} → Y ≉ₘ X → dₘ (σ X) (σ Y) ≡ 0 → dₘ (σ X) (σ Y) < dₘ X Y
  dₘ-eqStrContracting {X} {Y} Y≉X d[σX,σY]≡0 = begin
    dₘ (σ X) (σ Y) ≡⟨ d[σX,σY]≡0 ⟩
    0              <⟨ n≢0⇒0<n (Y≉X ∘ ≈ₘ-sym ∘ dₘ≡0⇒X≈Y) ⟩
    dₘ X Y         ∎
    where open ≤-Reasoning
    
  dₘ-strContracting : σ StrContrOver dₘ
  dₘ-strContracting {X} {Y} Y≉X with max[t]∈t 0 (λ i → dₜ (X i) (Y i)) | max[t]∈t 0 (λ i → dₜ (σ X i) (σ Y i))
  ...   | inj₁ dXY≡0             | _                          = contradiction (≈ₘ-sym (dₘ≡0⇒X≈Y dXY≡0)) Y≉X
  ...   | inj₂ _                 | inj₁ d[σX,σY]≡0            = dₘ-eqStrContracting Y≉X d[σX,σY]≡0
  ...   | inj₂ (k , dₘXY≡dₜXₖYₖ) | inj₂ (l , dₘσXσY≡dₜσXₗσYₗ) = begin
    dₘ (σ X) (σ Y)     ≡⟨ dₘσXσY≡dₜσXₗσYₗ ⟩
    dₜ (σ X l) (σ Y l) <⟨ dₜ-strContracting Xₖ≉Yₖ dₜ≤dₜσXₗσYₗ dₜ≤dₜXₖYₖ ⟩
    dₜ (X k) (Y k)     ≡⟨ sym dₘXY≡dₜXₖYₖ ⟩
    dₘ X Y             ∎
    where

    open ≤-Reasoning

    Xₖ≉Yₖ : X k ≉ₜ Y k
    Xₖ≉Yₖ Xₖ≈Yₖ = Y≉X (≈ₘ-sym (dₘ≡0⇒X≈Y (trans dₘXY≡dₜXₖYₖ (x≈y⇒dₜ≡0 Xₖ≈Yₖ))))

    dₜ≤dₜσXₗσYₗ : ∀ i → dₜ (σ X i) (σ Y i) ≤ dₜ (σ X l) (σ Y l)
    dₜ≤dₜσXₗσYₗ i = subst (dₜ (σ X i) (σ Y i) ≤_) dₘσXσY≡dₜσXₗσYₗ (MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) dₜ (σ X) (σ Y) i)

    dₜ≤dₜXₖYₖ : ∀ i → dₜ (X i) (Y i) ≤ dₜ (X k) (Y k)
    dₜ≤dₜXₖYₖ i = subst (dₜ (X i) (Y i) ≤_) dₘXY≡dₜXₖYₖ (MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) dₜ X Y i)
