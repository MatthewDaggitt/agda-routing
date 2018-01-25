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
open import RoutingLib.Function.Distance using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)
import RoutingLib.Function.Distance.MaxLift as MaxLift

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step3_InconsistentTableMetric as Step3

import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Preludeᶜ
import RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StateMetric as Step3ᶜ

module RoutingLib.Routing.BellmanFord.PathVector.Step4_ConsistentTableMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
    
  open Step3ᶜ 𝓡𝓟ᶜ 𝓢𝓒
  open Preludeᶜ 𝓡𝓟ᶜ 𝓢𝓒 using () renaming
    ( H    to Hᶜ
    ; 1≤H  to 1≤Hᶜ
    ; ℝ𝕋ₛ to ℝ𝕋ₛᶜ
    )

  -------------------------------------------
  -- An ultrametric over consistent tables --
  -------------------------------------------

  dₜᶜ : ∀ {x y} → 𝑪ₜ x → 𝑪ₜ y → ℕ
  dₜᶜ xᶜ yᶜ = dᵢ (toCTable xᶜ) (toCTable yᶜ)
  
  dₜᶜ-cong : ∀ {x y w z} (wᶜ : 𝑪ₜ w) (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) (zᶜ : 𝑪ₜ z) →
             w ≈ₜ y → x ≈ₜ z → dₜᶜ wᶜ xᶜ ≡ dₜᶜ yᶜ zᶜ
  dₜᶜ-cong wᶜ xᶜ yᶜ zᶜ w≈y x≈z = dᵢ-cong {x = toCTable wᶜ} {y = toCTable yᶜ} {u = toCTable xᶜ} {v = toCTable zᶜ} w≈y x≈z
  
  dₜᶜ-sym : ∀ {x y} (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) → dₜᶜ xᶜ yᶜ ≡ dₜᶜ yᶜ xᶜ
  dₜᶜ-sym xᶜ yᶜ = dᵢ-sym (toCTable xᶜ) (toCTable yᶜ)
  
  x≈y⇒dₜᶜ≡0 : ∀ {x y} (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) → x ≈ₜ y → dₜᶜ xᶜ yᶜ ≡ 0
  x≈y⇒dₜᶜ≡0 xᶜ yᶜ x≈y = x≈y⇒dᵢ≡0 {toCTable xᶜ} {toCTable yᶜ} x≈y
  
  dₜᶜ≡0⇒x≈y : ∀ {x y} (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) → dₜᶜ xᶜ yᶜ ≡ 0 → x ≈ₜ y
  dₜᶜ≡0⇒x≈y xᶜ yᶜ d≡0 = dᵢ≡0⇒x≈y {toCTable xᶜ} {toCTable yᶜ} d≡0

  postulate dₜᶜ-strContr : ∀ {k l X Y} → X l ≉ₜ Y l →
                           (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) (σXᶜ : 𝑪ₘ (σ X)) (σYᶜ : 𝑪ₘ (σ Y)) →
                           (∀ i → dₜᶜ (σXᶜ i) (σYᶜ i) ≤ dₜᶜ (σXᶜ k) (σYᶜ k)) →
                           (∀ i → dₜᶜ (Xᶜ i)  (Yᶜ i)  ≤ dₜᶜ (Xᶜ l)  (Yᶜ l)) →
                           dₜᶜ (σXᶜ k) (σYᶜ k) < dₜᶜ (Xᶜ l) (Yᶜ l)


  postulate dₜᶜ-maxTriIneq : ∀ {x y z} (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) (zᶜ : 𝑪ₜ z) →
                             dₜᶜ xᶜ zᶜ ≤ dₜᶜ xᶜ yᶜ ⊔ dₜᶜ yᶜ zᶜ

  postulate dₜᶜ-bounded : ∃ λ n → ∀ {x y} (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) → dₜᶜ xᶜ yᶜ ≤ n
