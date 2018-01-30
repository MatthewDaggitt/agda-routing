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

import RoutingLib.Routing.BellmanFord as BellmanFord

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step2_InconsistentRouteMetric as Step2

import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Preludeᶜ
import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_RouteMetric as Step2ᶜ

module RoutingLib.Routing.BellmanFord.PathVector.Step3_ConsistentRouteMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open BellmanFord 𝓡𝓟ᶜ using () renaming (σ to σᶜ)
  open RoutingProblem 𝓡𝓟ᶜ using () renaming (≈-refl to ≈ᶜ-refl; ≈-sym to ≈ᶜ-sym)

  open Step2ᶜ 𝓡𝓟ᶜ 𝓢𝓒
  open Preludeᶜ 𝓡𝓟ᶜ 𝓢𝓒 using () renaming
    ( H    to Hᶜ
    ; 1≤H  to 1≤Hᶜ
    )

  -------------------------------------------
  -- An ultrametric over consistent tables --
  -------------------------------------------

  abstract
  
    dᵣᶜ : ∀ {x y} → 𝑪 x → 𝑪 y → ℕ
    dᵣᶜ xᶜ yᶜ = d (toCRoute xᶜ) (toCRoute yᶜ)
  
    dᵣᶜ-cong : ∀ {x y w z} (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
               w ≈ y → x ≈ z → dᵣᶜ wᶜ xᶜ ≡ dᵣᶜ yᶜ zᶜ
    dᵣᶜ-cong wᶜ xᶜ yᶜ zᶜ w≈y x≈z = d-cong
      {x = toCRoute wᶜ} {y = toCRoute yᶜ}
      {u = toCRoute xᶜ} {v = toCRoute zᶜ} w≈y x≈z
    
    dᵣᶜ-sym : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ ≡ dᵣᶜ yᶜ xᶜ
    dᵣᶜ-sym xᶜ yᶜ = d-sym (toCRoute xᶜ) (toCRoute yᶜ)
    
    x≈y⇒dᵣᶜ≡0 : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → x ≈ y → dᵣᶜ xᶜ yᶜ ≡ 0
    x≈y⇒dᵣᶜ≡0 xᶜ yᶜ x≈y = x≈y⇒d≡0 {toCRoute xᶜ} {toCRoute yᶜ} x≈y
    
    dᵣᶜ≡0⇒x≈y : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ ≡ 0 → x ≈ y
    dᵣᶜ≡0⇒x≈y xᶜ yᶜ d≡0 = d≡0⇒x≈y {toCRoute xᶜ} {toCRoute yᶜ} d≡0
  
    dᵣᶜ-maxTriIneq : ∀ {x y z} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
                    dᵣᶜ xᶜ zᶜ ≤ dᵣᶜ xᶜ yᶜ ⊔ dᵣᶜ yᶜ zᶜ
    dᵣᶜ-maxTriIneq xᶜ yᶜ zᶜ = d-maxTriIneq (toCRoute xᶜ) (toCRoute yᶜ) (toCRoute zᶜ)

    dᵣᶜ-bounded : ∃ λ n → ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ ≤ n
    dᵣᶜ-bounded = Hᶜ , λ xᶜ yᶜ → d≤H (toCRoute xᶜ) (toCRoute yᶜ)

    dᵣᶜ-strContrOrbits : ∀ {X r s} → X r s ≉ σ X r s →
                        (Xᶜ : 𝑪ₘ X) (σXᶜ : 𝑪ₘ (σ X)) (σ²Xᶜ : 𝑪ₘ (σ (σ X))) →
                        (∀ {u v} → X u v ≉ σ X u v → dᵣᶜ (Xᶜ u v) (σXᶜ u v) ≤ dᵣᶜ (Xᶜ r s) (σXᶜ r s)) →
                        ∀ i j → dᵣᶜ (σXᶜ i j) (σ²Xᶜ i j) < dᵣᶜ (Xᶜ r s) (σXᶜ r s)
    dᵣᶜ-strContrOrbits {X} {r} {s} Xᵣₛ≉σXᵣₛ Xᶜ σXᶜ σ²Xᶜ dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ i j = begin
      d (toCMatrix σXᶜ i j) (toCMatrix σ²Xᶜ i j) ≡⟨ d-cong toMσXᶜᵢⱼ≈σᶜX'ᵢⱼ toMσ²Xᶜᵢⱼ≈σᶜσX'ᵢⱼ ⟩
      d (σᶜ X' i j)         (σᶜ σX' i j)         <⟨ d-strContr Xᵣₛ≉σXᵣₛ less i j ⟩
      d (X' r s)            (σX' r s)           ≡⟨⟩
      d (toCMatrix Xᶜ r s)  (toCMatrix σXᶜ r s) ∎
      where
      
      open ≤-Reasoning
      
      X'  = toCMatrix Xᶜ
      σX' = toCMatrix σXᶜ
      
      toMσXᶜᵢⱼ≈σᶜX'ᵢⱼ : toCMatrix σXᶜ i j ≈ᶜ σᶜ X' i j
      toMσXᶜᵢⱼ≈σᶜX'ᵢⱼ = σ-toCMatrix-commute Xᶜ σXᶜ i j

      toMσ²Xᶜᵢⱼ≈σᶜσX'ᵢⱼ : toCMatrix σ²Xᶜ i j ≈ᶜ σᶜ σX' i j
      toMσ²Xᶜᵢⱼ≈σᶜσX'ᵢⱼ = σ-toCMatrix-commute σXᶜ σ²Xᶜ i j
      
      less : ∀ u v → X' u v ≉ᶜ σX' u v → d (X' u v) (σX' u v) ≤ d (X' r s) (σX' r s)
      less u v X'ᵤᵥ≉σX'ᵤᵥ = dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ X'ᵤᵥ≉σX'ᵤᵥ
