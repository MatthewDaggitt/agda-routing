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
open import RoutingLib.Routing.Model using (AdjacencyMatrix)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

import RoutingLib.Routing.BellmanFord.Asynchronous as AsyncBellmanFord
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
  {n} (network : Epoch → AdjacencyMatrix algebra n)
  
  where

open AsyncBellmanFord algebra network hiding (AdjacencyMatrix)
open SyncMetrics isRoutingAlgebra isFinite using (h; dₜ)
open SyncMetricProperties isRoutingAlgebra isFinite

module _ (e : Epoch) (p : Subset n) where

  open Metrics isRoutingAlgebra isFinite p hiding (dₜ)
  open MetricProperties isRoutingAlgebra isFinite p
  open SyncStrictlyContracting isRoutingAlgebra isFinite isStrictlyIncreasing (Aₜ e p)

  private
    F : RoutingMatrix → RoutingMatrix
    F = Fₜ e p
  
  dₜFXᵢFYᵢ<DˢXY : ∀ {X Y} → WellFormed p X → WellFormed p Y →
                 Y ≉ₘ[ p ] X → ∀ i → dₜᶜ i (F X i) (F Y i) < Dˢ X Y
  dₜFXᵢFYᵢ<DˢXY {X} {Y} wfX wfY Y≉X i with i ∈? p
  ... | no  _ = Y≉ₚX⇒0<DˢXY Y≉X
  ... | yes _ = max[t]<x (Y≉ₚX⇒0<DˢXY Y≉X) (λ j → dσXᵢⱼσYᵢⱼ<v X Y i j (Y≉ₚX⇒0<DˢXY Y≉X) (λ k _ → d≤Dˢ-wf wfX wfY k j))

  Dˢ-strContr-F : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X →
                  Dˢ (F X) (F Y) < Dˢ X Y
  Dˢ-strContr-F wfX wfY Y≉X = max[t]<x (Y≉ₚX⇒0<DˢXY Y≉X) (dₜFXᵢFYᵢ<DˢXY wfX wfY Y≉X)

  F-strContrOnOrbits : ∀ {X} → WellFormed p X → (F X) ≉ₘ[ p ] X →
                       Dˢ (F X) (F (F X)) < Dˢ X (F X)
  F-strContrOnOrbits {X} wfX FX≉X = Dˢ-strContr-F wfX (Fₜ-inactive e X) FX≉X

  F-strContrOnFP : ∀ {X} → WellFormed p X → ∀ {X*} → F X* ≈ₘ X* → X ≉ₘ[ p ] X* →
                   Dˢ X* (F X) < Dˢ X* X
  F-strContrOnFP {X} wfX {X*} FX*≈X* X≉X* = begin
    Dˢ X*     (F X) ≡⟨ Dˢ-cong (≈ₘ-sym FX*≈X*) (≈ₘ-refl {x = Fₜ e p X}) ⟩
    Dˢ (F X*) (F X) <⟨ Dˢ-strContr-F (X*-wf e p FX*≈X*) wfX X≉X* ⟩
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
  ; F-strContrOnOrbits = F-strContrOnOrbits
  ; F-strContrOnFP     = F-strContrOnFP
  }
