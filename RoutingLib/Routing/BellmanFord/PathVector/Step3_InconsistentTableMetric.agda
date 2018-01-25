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
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m; m<n⇒n≢0; ≤-stepsʳ; +-monoʳ-≤; +-monoʳ-<; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Function.Distance using (Ultrametric; IsUltrametric; MaxTriangleIneq; Bounded)
import RoutingLib.Function.Distance.MaxLift as MaxLift

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step2_InconsistentRouteMetric as Step2

module RoutingLib.Routing.BellmanFord.PathVector.Step3_InconsistentTableMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step2 𝓟𝓢𝓒

  dₜⁱ-ultrametric : Ultrametric _
  dₜⁱ-ultrametric = MaxLift.ultrametric {n = n} (λ _ → _) (λ _ → dᵣⁱ-ultrametric)

  open Ultrametric dₜⁱ-ultrametric public using ()
    renaming
    ( d    to dₜⁱ
    ; 0⇒eq to dₜⁱ≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒dₜⁱ≡0
    ; sym  to dₜⁱ-sym
    )

  dₜⁱ-bounded : Bounded ℝ𝕋ₛ dₜⁱ
  dₜⁱ-bounded = MaxLift.bounded (λ _ → S) dᵣⁱ dᵣⁱ-bounded
  
  XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY : ∀ {X Y Z} → 𝑰ₜ X → 𝑪ₜ Y → 𝑪ₜ Z → dₜⁱ X Z ≤ dₜⁱ X Y
  XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY Xⁱ Yᶜ Zᶜ = {!!} --≤-reflexive (trans (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Zᶜ) (sym (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Yᶜ)))
    
  XᶜYᶜZⁱ⇒dₜⁱXZ≤dₜⁱYZ : ∀ {X Y Z} → 𝑪ₜ X → 𝑪ₜ Y → 𝑰ₜ Z → dₜⁱ X Z ≤ dₜⁱ Y Z
  XᶜYᶜZⁱ⇒dₜⁱXZ≤dₜⁱYZ {X} {Y} {Z} Xᶜ Yᶜ Zⁱ = subst₂ _≤_ (dₜⁱ-sym Z X) (dₜⁱ-sym Z Y) (XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY Zⁱ Yᶜ Xᶜ)



  dₜⁱ-strContr : ∀ {k l X Y} → X l ≉ₜ Y l → σ X k ≉ₜ σ Y k →
                 𝑰ₜ (X l) ⊎ 𝑰ₜ (Y l) → 𝑰ₜ (σ X k) ⊎ 𝑰ₜ (σ Y k) →
                 --(∀ i → dₜ (σ X i) (σ Y i) ≤ Hᶜ + dₜⁱ (σ X k) (σ Y k)) →
                 --(∀ i → dₜ (X i)   (Y i)   ≤ Hᶜ + dₜⁱ (X l)   (Y l)) →
                 dₜⁱ (σ X k) (σ Y k) < dₜⁱ (X l) (Y l)
  dₜⁱ-strContr {k} {l} {X} {Y} Xₗ≉Yₗ σXₖ≉σYₖ Xₗⁱ⊎Yₗⁱ σXₖⁱ⊎σYₖⁱ with max[t]∈t 0 (λ j → dᵣⁱ (X l j) (Y l j))
  ... | inj₁ dₜⁱXₗKₗ≡0           = {!!}
  ... | inj₂ (m , dₜⁱ≡dᵣXₗₘYₗₘ)  = {!!}
