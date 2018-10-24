open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (module ≤-Reasoning)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Data.Product using (∃; _,_; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst)
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
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
open import RoutingLib.Routing.Model as Model using (AdjacencyMatrix)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Properties as SyncBellmanFordProperties
import RoutingLib.Routing.BellmanFord.Asynchronous as AsyncBellmanFord
import RoutingLib.Routing.BellmanFord.Asynchronous.PathVector.Convergence.Metrics as Metrics
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Properties as SyncMetricProperties

module RoutingLib.Routing.BellmanFord.Asynchronous.PathVector.Convergence.Properties
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  (1≤n : 1 ≤ n) (p : Subset n)
  where

open Model algebra n
open Metrics isPathAlgebra A p 
open SyncMetricProperties isPathAlgebra A 1≤n public

------------------------------------------------------------------------
-- Properties of dₜᶜ

private module Conditionₜ = Condition dₜ (_∈? p)

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

Dˢ≡0⇒X≈ₛY : ∀ {X Y} → Dˢ X Y ≡ 0 → X ≈ₘ[ p ] Y
Dˢ≡0⇒X≈ₛY Dˢ≡0 i∈p = Conditionₜ.≡0⇒x≈y dₜ≡0⇒x≈y i∈p (MaxLiftₘ.d≡0⇒dᵢ≡0 Dˢ≡0 _)

dₜ≤Dˢ : ∀ X Y i → (i ∈ p ⊎ X i ≈ₜ Y i) → dₜ (X i) (Y i) ≤ Dˢ X Y
dₜ≤Dˢ X Y i cond  = subst (_≤ Dˢ X Y) (Conditionₜ.dᶜ≡d⁺ i (X i) (Y i) (map₂ x≈y⇒dₜ≡0 cond)) (MaxLiftₘ.dᵢ≤d X Y i)

d≤Dˢ : ∀ X Y i j → (i ∈ p ⊎ X i ≈ₜ Y i) → d (X i j) (Y i j) ≤ Dˢ X Y
d≤Dˢ X Y i j op = ≤-trans (d≤dₜ (X i) (Y i) j) (dₜ≤Dˢ X Y i op)

d≤Dˢ-wf : ∀ {X Y} → WellFormed p X → WellFormed p Y → ∀ i j → d (X i j) (Y i j) ≤ Dˢ X Y
d≤Dˢ-wf {X} {Y} wfX wfY i j with i ∈? p
... | yes i∈p = d≤Dˢ X Y i j (inj₁ i∈p)
... | no  i∉p = d≤Dˢ X Y i j (inj₂ (WellFormed-cong wfX wfY i∉p))

Y≉ₚX⇒0<DˢXY : ∀ {X Y} → Y ≉ₘ[ p ] X → 0 < Dˢ X Y
Y≉ₚX⇒0<DˢXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₛ-sym ∘ Dˢ≡0⇒X≈ₛY)
