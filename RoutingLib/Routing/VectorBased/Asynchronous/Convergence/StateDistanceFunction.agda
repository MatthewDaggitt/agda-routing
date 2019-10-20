open import Data.Fin.Subset using (Subset; _∈_)

open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.VectorBased.Asynchronous as AsyncVectorBasedRouting
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.RouteDistanceFunction

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.StateDistanceFunction
  {a b ℓ} (alg : RawRoutingAlgebra a b ℓ)
  (isRoutingAlgebra : IsRoutingAlgebra alg)
  {n} (A : AdjacencyMatrix alg n)
  (routeDistanceFunction : RouteDistanceFunction isRoutingAlgebra A)
  (p : Subset n)
  where

open RawRoutingAlgebra alg

open import Data.Bool using (if_then_else_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Product using (∃; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Level using (_⊔_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Data.Table using (max; zipWith)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift
open import RoutingLib.Function.Metric.Nat 
import RoutingLib.Relation.Nullary.Decidable as Dec

-- open import RoutingLib.Routing alg n
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence
open import RoutingLib.Routing.VectorBased.Synchronous alg A
open import RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties isRoutingAlgebra A

private
  F² : RoutingMatrix → RoutingMatrix
  F² = F ∘ F

open RouteDistanceFunction routeDistanceFunction

------------------------------------------------------------------------
-- Lifting the distance function

-- The distance between two routing tables
d : RoutingTable → RoutingTable → ℕ
d x y = max 0 (zipWith r x y)

-- The conditional distance between two routing tables
dᵢ : ∀ (i : Fin n) → RoutingTable → RoutingTable → ℕ
dᵢ i x y = if ⌊ i ∈? p ⌋ then d x y else 0

-- The distance between two routing states
D : RoutingMatrix → RoutingMatrix → ℕ
D X Y = max 0 (λ i → dᵢ i (X i) (Y i))


------------------------------------------------------------------------
-- Properties of d

private
  module MaxLiftₜ = MaxLift ℝ𝕋ₛⁱ (λ _ → r)

d-isQuasiSemiMetric : IsQuasiSemiMetric _ d
d-isQuasiSemiMetric = MaxLiftₜ.isQuasiSemiMetric r-isQuasiSemiMetric

open IsQuasiSemiMetric d-isQuasiSemiMetric public
  using () renaming
  ( cong              to d-cong
  ; eq⇒0              to x≈y⇒d≡0
  ; 0⇒eq              to d≡0⇒x≈y
  )

d-bounded : ∃ λ dₘₐₓ → ∀ x y → d x y ≤ dₘₐₓ
d-bounded = MaxLiftₜ.bounded r-bounded

r≤d : ∀ x y i → r (x i) (y i) ≤ d x y
r≤d = MaxLiftₜ.dᵢ≤d

------------------------------------------------------------------------
-- Properties of D

private
  module Conditionₜ = Condition d (_∈? p)
  module MaxLiftₘ = MaxLift ℝ𝕄ₛⁱ dᵢ

D≡0⇒X≈ₛY : ∀ {X Y} → D X Y ≡ 0 → X ≈ₘ[ p ] Y
D≡0⇒X≈ₛY D≡0 i∈p = Conditionₜ.≡0⇒x≈y d≡0⇒x≈y i∈p (MaxLiftₘ.d≡0⇒dᵢ≡0 D≡0 _)

Y≉ₚX⇒0<DXY : ∀ {X Y} → Y ≉ₘ[ p ] X → 0 < D X Y
Y≉ₚX⇒0<DXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₛ-sym ∘ D≡0⇒X≈ₛY)

d≤D : ∀ X Y i → (i ∈ p ⊎ X i ≈ₜ Y i) → d (X i) (Y i) ≤ D X Y
d≤D X Y i cond  = subst (_≤ D X Y) (Conditionₜ.dᶜ≡d⁺ i (X i) (Y i) (map₂ x≈y⇒d≡0 cond)) (MaxLiftₘ.dᵢ≤d X Y i)

r≤D : ∀ X Y i j → (i ∈ p ⊎ X i ≈ₜ Y i) → r (X i j) (Y i j) ≤ D X Y
r≤D X Y i j op = ≤-trans (r≤d (X i) (Y i) j) (d≤D X Y i op)

r≤D-wf : ∀ {X Y} → WellFormed p X → WellFormed p Y → ∀ i j → r (X i j) (Y i j) ≤ D X Y
r≤D-wf {X} {Y} wfX wfY i j with i ∈? p
... | yes i∈p = r≤D X Y i j (inj₁ i∈p)
... | no  i∉p = r≤D X Y i j (inj₂ (WellFormed-cong wfX wfY i∉p))

------------------------------------------------------------------------
-- Strictly contracting proofs

-- These two lemmas are a mess as can't pattern match on `i ∈? p` directly
-- as it unfolds the adjacency matrix

{-
d[FXᵢ,F²Xᵢ]<D[X,FX] : ∀ {X} → WellFormed p X → F X ≉ₘ[ p ] X →
                      ∀ i → dᵢ i (F X i) (F² X i) < D X (F X)
d[FXᵢ,F²Xᵢ]<D[X,FX] {X} wfX FX≉X i with Y≉ₚX⇒0<DXY FX≉X
... | 0<DXY with max[t]<x 0<DXY (r-strContrOrbits 0<DXY (r≤D-wf wfX (F′-inactive e p X)) i)
...   | d[FXᵢ,F²Xᵢ]<D[X,FX] = Dec.[
      (λ i∈p → subst (_< D X (F X)) (sym (Condition.accept d (_∈? p) i∈p)) d[FXᵢ,F²Xᵢ]<D[X,FX]) ,
      (λ i∉p → subst (_< D X (F X)) (sym (Condition.reject d (_∈? p) i∉p)) 0<DXY)
    ] (i ∈? p)

dᵢ[X*ᵢ,FXᵢ]<D[X*,X] : ∀ {X*} → F X* ≈ₘ X* → ∀ {X} → WellFormed p X → X ≉ₘ[ p ] X* →
                      ∀ i → dᵢ i (X* i) (F X i) < D X* X
dᵢ[X*ᵢ,FXᵢ]<D[X*,X] {X*} FX*≈X* {X} wfX X≉X* i with Y≉ₚX⇒0<DXY X≉X*
... | 0<DXY with max[t]<x 0<DXY (r-strContrFP FX*≈X* 0<DXY (r≤D-wf (X*-wf e p FX*≈X*) wfX) i)
...   | d[FXᵢ,F²Xᵢ]<D[X,FX] = Dec.[
      (λ i∈p → subst (_< D X* X) (sym (Condition.accept d (_∈? p) i∈p)) d[FXᵢ,F²Xᵢ]<D[X,FX]) ,
      (λ i∉p → subst (_< D X* X) (sym (Condition.reject d (_∈? p) i∉p)) 0<DXY)
    ] (i ∈? p)

Fₜ-strContrOnOrbits : ∀ {X} → WellFormed p X → F X ≉ₘ[ p ] X →
                      D (F X) (F² X) < D X (F X)
Fₜ-strContrOnOrbits {X} wfX FX≉X = max[t]<x (Y≉ₚX⇒0<DXY FX≉X) (d[FXᵢ,F²Xᵢ]<D[X,FX] wfX FX≉X)

Fₜ-strContrOnFP : ∀ {X} → WellFormed p X → ∀ {X*} → F X* ≈ₘ X* → X ≉ₘ[ p ] X* →
                  D X* (F X) < D X* X
Fₜ-strContrOnFP {X} wfX {X*} FX*≈X* X≉X* = max[t]<x (Y≉ₚX⇒0<DXY X≉X*) (dᵢ[X*ᵢ,FXᵢ]<D[X*,X] FX*≈X* wfX X≉X*)
-}
