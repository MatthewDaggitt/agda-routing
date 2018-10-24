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
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Properties as PathAlgebraProperties
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Consistency as Consistency
open import RoutingLib.Routing.Model using (AdjacencyMatrix)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

import RoutingLib.Routing.BellmanFord.Asynchronous as AsyncBellmanFord
import RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Properties as AsyncBellmanFordProperties
import RoutingLib.Routing.BellmanFord.Asynchronous.PathVector.Convergence.Metrics as Metrics
import RoutingLib.Routing.BellmanFord.Asynchronous.PathVector.Convergence.Properties as MetricProperties
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Properties as SyncBellmanFordProperties
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Metrics as SyncMetrics
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Properties as SyncMetricProperties
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.StrictlyContracting as SyncStrictlyContracting

module RoutingLib.Routing.BellmanFord.Asynchronous.PathVector.Convergence.StrictlyContracting
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  (network : Epoch → AdjacencyMatrix algebra n)
  (1≤n : 1 ≤ n)
  where

open IsCertifiedPathAlgebra isPathAlgebra
open AsyncBellmanFord algebra network
open AsyncBellmanFordProperties algebra isRoutingAlgebra network

module _ (e : Epoch) (p : Subset n) where

  open Metrics isPathAlgebra (Aₜ e p) p public
  open MetricProperties isPathAlgebra (Aₜ e p) 1≤n p public
  open PathAlgebraProperties isPathAlgebra
  open SyncBellmanFordProperties algebra isPathAlgebra (Aₜ e p)
  open SyncStrictlyContracting isPathAlgebra isStrictlyIncreasing (Aₜ e p) 1≤n
  
  private
    σ : RoutingMatrix → RoutingMatrix
    σ = σₜ e p

------------------------------------------------------------------------
-- dₜ is contracting in the right ways

  dₜσXᵢσ²Xᵢ<DˢXσX : ∀ {X} → WellFormed p X → σ X ≉ₘ[ p ] X →
                ∀ i → dₜᶜ i (σ X i) (σ (σ X) i) < Dˢ X (σ X)
  dₜσXᵢσ²Xᵢ<DˢXσX {X} wfX σX≉X i with i ∈? p
  ... | no  _ = Y≉ₚX⇒0<DˢXY σX≉X
  ... | yes _ = max[t]<x 0<DˢXY (dᵣ-strContrOrbits 0<DˢXY (d≤Dˢ-wf wfX (σₜ-inactive e X)) i)
    where 0<DˢXY = Y≉ₚX⇒0<DˢXY σX≉X
    
  dₜσXᵢσYᵢ<DˢXY : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X →
                 𝑪ₘ X → ∀ i → dₜᶜ i (σ X i) (σ Y i) < Dˢ X Y
  dₜσXᵢσYᵢ<DˢXY {X} {Y} wfX wfY Y≉X Xᶜ i with i ∈? p
  ... | no  _ = Y≉ₚX⇒0<DˢXY Y≉X
  ... | yes _ = max[t]<x 0<DˢXY (dᵣ-strContrOn𝑪 Xᶜ 0<DˢXY (d≤Dˢ-wf wfX wfY) i)
    where 0<DˢXY = Y≉ₚX⇒0<DˢXY Y≉X

------------------------------------------------------------------------
-- Dˢ is contracting in the right ways

  σₜ-strContrOnOrbits : ∀ {X} → WellFormed p X → (σ X) ≉ₘ[ p ] X →
                       Dˢ (σ X) (σ (σ X)) < Dˢ X (σ X)
  σₜ-strContrOnOrbits {X} wfX σX≉X = max[t]<x (Y≉ₚX⇒0<DˢXY σX≉X) (dₜσXᵢσ²Xᵢ<DˢXσX wfX σX≉X)
  
  σₜ-strContrOn𝑪 : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X → 𝑪ₘ X →
                   Dˢ (σ X) (σ Y) < Dˢ X Y
  σₜ-strContrOn𝑪 wfX wfY Y≉X Xᶜ = max[t]<x (Y≉ₚX⇒0<DˢXY Y≉X) (dₜσXᵢσYᵢ<DˢXY wfX wfY Y≉X Xᶜ)

  σₜ-strContrOnFP : ∀ {X} → WellFormed p X → ∀ {X*} → σ X* ≈ₘ X* → X ≉ₘ[ p ] X* →
                   Dˢ X* (σ X) < Dˢ X* X
  σₜ-strContrOnFP {X} wfX {X*} σX*≈X* X≉X* = begin
    Dˢ X*     (σ X) ≡⟨ Dˢ-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σₜ e p X}) ⟩
    Dˢ (σ X*) (σ X) <⟨ σₜ-strContrOn𝑪 (X*-wf e p σX*≈X*) wfX X≉X* (fixedPointᶜ σX*≈X*) ⟩
    Dˢ X*     X     ∎
    where open ≤-Reasoning
 
ultrametricConditions : UltrametricConditions δ∥
ultrametricConditions = record
  { dᵢ                 = λ e p → dₜ e p
  ; dᵢ-cong            = λ e p → dₜ-cong e p
  ; x≈y⇒dᵢ≡0           = λ e p → x≈y⇒dₜ≡0 e p
  ; dᵢ≡0⇒x≈y           = λ e p → dₜ≡0⇒x≈y e p
  ; dᵢ-bounded         = λ e p → proj₁ (dₜ-bounded e p) , proj₂ (dₜ-bounded e p)
  ; element            = I
  
  ; F-strContrOnOrbits = σₜ-strContrOnOrbits
  ; F-strContrOnFP     = σₜ-strContrOnFP
  ; F-inactive         = σₜ-inactive
  }
