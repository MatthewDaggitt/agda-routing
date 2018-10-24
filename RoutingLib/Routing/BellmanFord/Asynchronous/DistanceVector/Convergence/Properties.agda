open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (module ≤-Reasoning)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning; n≢0⇒0<n)
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift
import RoutingLib.Function.Metric as Metric
import RoutingLib.Relation.Binary.Reasoning.PartialOrder as PO-Reasoning

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
import RoutingLib.Routing.Model as Model
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Properties as SyncBellmanFordProperties
import RoutingLib.Routing.BellmanFord.Asynchronous as AsyncBellmanFord
import RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Convergence.Metrics as Metrics
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Properties as SyncMetricProperties

module RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Convergence.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  {n} (p : Subset n)
  where

open Model algebra n
open Metrics isRoutingAlgebra isFinite p 
open SyncMetricProperties isRoutingAlgebra isFinite

------------------------------------------------------------------------
-- Properties of dₜᶜ

private module Conditionₜ = Condition (dₜ {n}) (_∈? p)

dₜᶜ-cong : ∀ i → dₜᶜ i Preserves₂ _≈ₜ_ ⟶ _≈ₜ_ ⟶ _≡_
dₜᶜ-cong = Conditionₜ.cong′ dₜ-cong

dₜᶜ-sym : ∀ i x y → dₜᶜ i x y ≡ dₜᶜ i y x
dₜᶜ-sym = Conditionₜ.sym dₜ-sym

------------------------------------------------------------------------
-- Properties of Dˢ

private module MaxLiftₘ = MaxLift ℝ𝕄ₛⁱ dₜᶜ

Dˢ-sym : ∀ X Y → Dˢ X Y ≡ Dˢ Y X
Dˢ-sym = MaxLiftₘ.sym (dₜᶜ-sym _)

Dˢ-cong : Dˢ Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
Dˢ-cong = MaxLiftₘ.cong (dₜᶜ-cong _)

postulate Dˢ-congˢ : Dˢ Preserves₂ (_≈ₘ[ p ]_) ⟶ (_≈ₘ[ p ]_) ⟶ _≡_
-- Dˢ-congˢ = {!!} --MaxLiftₘ.congˢ dₜ-cong

postulate Dˢ≡0⇒X≈ₛY : ∀ {X Y} → Dˢ X Y ≡ 0 → X ≈ₘ[ p ] Y
-- Dˢ≡0⇒X≈ₛY Dˢ≡0 = {!MaxLiftₘ.d≡0⇒x≈y ? !}

postulate dₜ≤Dˢ : ∀ X Y i → (i ∈ p ⊎ X i ≈ₜ Y i) → dₜ (X i) (Y i) ≤ Dˢ X Y
{-
dₜ≤Dˢ X Y i (inj₁ i∈p)  = SubsetMaxLift.dᵢ≤dˢ ℝ𝕄ₛⁱ dₜ p X Y i∈p
dₜ≤Dˢ X Y i (inj₂ Xᵢ≈Yᵢ) = x≤max[t] 0 (λ i → cond (X i) (Y i)) (inj₁ (≤-reflexive (x≈y⇒dₜ≡0 Xᵢ≈Yᵢ)))
-}

d≤Dˢ : ∀ X Y i j → (i ∈ p ⊎ X i ≈ₜ Y i) → d (X i j) (Y i j) ≤ Dˢ X Y
d≤Dˢ X Y i j op = ≤-trans (d≤dₜ (X i) (Y i) j) (dₜ≤Dˢ X Y i op)

d≤Dˢ-wf : ∀ {X Y} → WellFormed p X → WellFormed p Y → ∀ i j → d (X i j) (Y i j) ≤ Dˢ X Y
d≤Dˢ-wf {X} {Y} wfX wfY i j with i ∈? p
... | yes i∈p = d≤Dˢ X Y i j (inj₁ i∈p)
... | no  i∉p = d≤Dˢ X Y i j (inj₂ (WellFormed-cong wfX wfY i∉p))

Y≉ₚX⇒0<DˢXY : ∀ {X Y} → Y ≉ₘ[ p ] X → 0 < Dˢ X Y
Y≉ₚX⇒0<DˢXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₛ-sym ∘ Dˢ≡0⇒X≈ₛY)
