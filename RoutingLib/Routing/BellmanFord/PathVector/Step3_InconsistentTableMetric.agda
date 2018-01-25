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
import RoutingLib.Function.Distance as Distance 
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
  open Distance ℝ𝕋ₛ using (Ultrametric; Bounded)

  dₜⁱ-ultrametric : Ultrametric
  dₜⁱ-ultrametric = MaxLift.ultrametric (λ _ → _) (λ _ → dᵣⁱ-ultrametric)

  open Ultrametric dₜⁱ-ultrametric public using ()
    renaming
    ( d    to dₜⁱ
    ; 0⇒eq to dₜⁱ≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒dₜⁱ≡0
    ; sym  to dₜⁱ-sym
    )

  dₜⁱ-bounded : Bounded dₜⁱ
  dₜⁱ-bounded = MaxLift.bounded (λ _ → S) dᵣⁱ dᵣⁱ-bounded
  
  XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY : ∀ {X Y Z} → 𝑰ₜ X → 𝑪ₜ Y → 𝑪ₜ Z → dₜⁱ X Z ≤ dₜⁱ X Y
  XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY Xⁱ Yᶜ Zᶜ = {!!}
    --≤-reflexive (trans (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Zᶜ) (sym (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Yᶜ)))
    
  XᶜYᶜZⁱ⇒dₜⁱXZ≤dₜⁱYZ : ∀ {X Y Z} → 𝑪ₜ X → 𝑪ₜ Y → 𝑰ₜ Z → dₜⁱ X Z ≤ dₜⁱ Y Z
  XᶜYᶜZⁱ⇒dₜⁱXZ≤dₜⁱYZ {X} {Y} {Z} Xᶜ Yᶜ Zⁱ =
    subst₂ _≤_ (dₜⁱ-sym Z X) (dₜⁱ-sym Z Y) (XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY Zⁱ Yᶜ Xᶜ)


{-
  dₜⁱ-strContrExt : ∀ {i j r s X Y} → X r s ≉ Y r s → σ X i j ≉ σ Y i j →
                    dᵣⁱ (σ X i j) (σ Y i j) < dᵣⁱ (X r s) (Y r s)
  dₜⁱ-strContrExt {i} {j} {r} {s} {X} {Y} Xᵣₛ≉Yᵣₛ σXᵢⱼ≉σYᵢⱼ
    with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X r s | σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ Y r s
  ... | inj₂ σXᵢⱼ≈Iᵢⱼ          | _                      = {!!}
  ... | _                      | inj₂ σYᵢⱼ≈Iᵢⱼ           = {!!}
  ... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) | inj₁ (l , σYᵢⱼ≈AᵢₗXₗⱼ) = {!!}

-}

  

  dₜⁱ-strContr : ∀ {i r X Y} → X r ≉ₜ Y r → σ X i ≉ₜ σ Y i →
                 𝑰ₜ (σ X i) ⊎ 𝑰ₜ (σ Y i) →
                 --(∀ k → dₜ (σ X k) (σ Y k) ≤ Hᶜ + dₜⁱ (σ X i) (σ Y i)) →
                 (∀ s → dₜⁱ (X s) (Y s) ≤ dₜⁱ (X r) (Y r)) →
                 dₜⁱ (σ X i) (σ Y i) < dₜⁱ (X r) (Y r)
  dₜⁱ-strContr {i} {r} {X} {Y} Xₗ≉Yₗ σXₖ≉σYₖ σXₖⁱ⊎σYₖⁱ dₜⁱ≤dₜⁱXᵣYᵣ
    with max[t]∈t 0 (λ j → dᵣⁱ (X r j) (Y r j))
       | max[t]∈t 0 (λ j → dᵣⁱ (σ X i j) (σ Y i j))
  ... | inj₁ dₜⁱXₗKₗ≡0           | _                 = contradiction (dₜⁱ≡0⇒X≈Y dₜⁱXₗKₗ≡0) Xₗ≉Yₗ
  ... | inj₂ (m , dₜⁱ≡dᵣXₗₘYₗₘ)  | inj₁ dₜⁱσXₖσYₖ≡0 = contradiction (dₜⁱ≡0⇒X≈Y dₜⁱσXₖσYₖ≡0) σXₖ≉σYₖ
  ... | inj₂ (s , dₜⁱ≡dᵣXᵣₛYᵣₛ)  | inj₂ (j , dₜⁱ≡dᵣσXᵢⱼσYᵢⱼ) with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ...   | inj₂ σXᵢⱼ≈Iᵢⱼ = {!!}
  ...   | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) = begin
    dₜⁱ (σ X i)        (σ Y i)          ≡⟨ dₜⁱ≡dᵣσXᵢⱼσYᵢⱼ ⟩
    dᵣⁱ (σ X i j)       (σ Y i j)       ≤⟨ {!!} ⟩
    dᵣⁱ (σ X i j)       (A i k ▷ Y k j) ≡⟨ dᵣⁱ-cong σXᵢⱼ≈AᵢₖXₖⱼ ≈-refl ⟩
    dᵣⁱ (A i k ▷ X k j) (A i k ▷ Y k j) <⟨ dᵣⁱ-strContr {!!} {!!} ⟩
    dᵣⁱ (X k j)         (Y k j)         ≤⟨ MaxLift.dᵢ≤d (λ _ → S) dᵣⁱ (X k) (Y k) j ⟩
    dₜⁱ (X k)          (Y k)            ≤⟨ dₜⁱ≤dₜⁱXᵣYᵣ k ⟩
    dₜⁱ (X r)          (Y r)            ∎
    where open ≤-Reasoning

  
