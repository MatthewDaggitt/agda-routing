open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_; module ≤-Reasoning)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning; n≢0⇒0<n)
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift
import RoutingLib.Function.Metric as Metric

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
open import RoutingLib.Routing.Model using (Network)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

import RoutingLib.Routing.BellmanFord.Asynchronous as AsyncBellmanFord
import RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Properties as BellmanFordProperties
import RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Convergence.Metrics as Metrics
import RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Convergence.Properties as MetricProperties
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Metrics as SyncMetrics
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Properties as SyncMetricProperties
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.StrictlyContracting as SyncStrictlyContracting

module RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Convergence.StrictlyContracting
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  {n} (network : Network algebra n)
  
  where

open AsyncBellmanFord algebra network hiding (AdjacencyMatrix)
open BellmanFordProperties algebra isRoutingAlgebra network
open SyncMetrics isRoutingAlgebra isFinite using (h; dₜ)
open SyncMetricProperties isRoutingAlgebra isFinite

module _ (e : Epoch) (p : Subset n) where

  open Metrics isRoutingAlgebra isFinite p hiding (dₜ)
  open MetricProperties isRoutingAlgebra isFinite p
  open SyncStrictlyContracting isRoutingAlgebra isFinite isStrictlyIncreasing (Aₜ e p)

  private
    σ : RoutingMatrix → RoutingMatrix
    σ = σₜ e p
  
  dₜσXᵢσYᵢ<DˢXY : ∀ {X Y} → WellFormed p X → WellFormed p Y →
                 Y ≉ₘ[ p ] X → ∀ i → dₜᶜ i (σ X i) (σ Y i) < Dˢ X Y
  dₜσXᵢσYᵢ<DˢXY {X} {Y} wfX wfY Y≉X i with i ∈? p
  ... | no  _ = Y≉ₚX⇒0<DˢXY Y≉X
  ... | yes _ = max[t]<x (Y≉ₚX⇒0<DˢXY Y≉X) (λ j → dσXᵢⱼσYᵢⱼ<v X Y i j (Y≉ₚX⇒0<DˢXY Y≉X) (λ k _ → d≤Dˢ-wf wfX wfY k j))

  σₜ-strContr : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X →
                  Dˢ (σ X) (σ Y) < Dˢ X Y
  σₜ-strContr wfX wfY Y≉X = max[t]<x (Y≉ₚX⇒0<DˢXY Y≉X) (dₜσXᵢσYᵢ<DˢXY wfX wfY Y≉X)

  σₜ-strContrOnOrbits : ∀ {X} → WellFormed p X → (σ X) ≉ₘ[ p ] X →
                       Dˢ (σ X) (σ (σ X)) < Dˢ X (σ X)
  σₜ-strContrOnOrbits {X} wfX σX≉X = σₜ-strContr wfX (σₜ-inactive e X) σX≉X

  σₜ-strContrOnFP : ∀ {X} → WellFormed p X → ∀ {X*} → σ X* ≈ₘ X* → X ≉ₘ[ p ] X* →
                   Dˢ X* (σ X) < Dˢ X* X
  σₜ-strContrOnFP {X} wfX {X*} σX*≈X* X≉X* = begin
    Dˢ X*     (σ X) ≡⟨ Dˢ-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σₜ e p X}) ⟩
    Dˢ (σ X*) (σ X) <⟨ σₜ-strContr (X*-wf e p σX*≈X*) wfX X≉X* ⟩
    Dˢ X*     X     ∎
    where open ≤-Reasoning
  
ultrametricConditions : UltrametricConditions δ∥
ultrametricConditions = record
  { dᵢ                 = λ _ _ → dₜ
  ; dᵢ-cong            = λ _ _ → dₜ-cong
  ; x≈y⇒dᵢ≡0           = λ _ _ → x≈y⇒dₜ≡0
  ; dᵢ≡0⇒x≈y           = λ _ _ → dₜ≡0⇒x≈y
  ; dᵢ-bounded         = λ _ _ → proj₁ (dₜ-bounded {n}) , proj₂ dₜ-bounded
  ; element            = I
  
  ; F-strContrOnOrbits = σₜ-strContrOnOrbits
  ; F-strContrOnFP     = σₜ-strContrOnFP
  ; F-inactive         = σₜ-inactive
  }
