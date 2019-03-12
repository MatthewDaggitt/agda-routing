--------------------------------------------------------------------------------
-- Proof that the metrics associated with a strictly increasing finite routing
-- algebra are strictly contracting in the right ways so as to ensure that
-- F∥ is an asynchronously metrically contracting operator (AMCO).
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.StrictlyContracting
  {a b ℓ}
  {algebra              : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra     : IsRoutingAlgebra algebra)
  (isFinite             : IsFinite algebra)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  where

open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_; module ≤-Reasoning)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning; n≢0⇒0<n)
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Relation.Binary.Reasoning.PartialOrder as POR
open import RoutingLib.Relation.Nullary.Decidable using ([_,_])

open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions
open import RoutingLib.Routing as Routing using (AdjacencyMatrix; Network)
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties
import RoutingLib.Routing.VectorBased.Core as CoreVectorBasedRouting
import RoutingLib.Routing.VectorBased.Core.Properties as CoreVectorBasedRoutingProperties
import RoutingLib.Routing.VectorBased.Asynchronous as DistanceVectorRouting
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Properties as DistanceVectorRoutingProperties
import RoutingLib.Routing.Algebra.Properties.FiniteRoutingAlgebra as FiniteRoutingAlgebraProperties
import RoutingLib.Routing.VectorBased.Asynchronous as AsyncVectorBased
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Metrics as Metrics
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Properties as MetricsProperties

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open FiniteRoutingAlgebraProperties isRoutingAlgebra isFinite

open Metrics isRoutingAlgebra isFinite
open MetricsProperties isRoutingAlgebra isFinite

--------------------------------------------------------------------------------
-- Proof for an individual adjacency matrix

module _ {n} (A : AdjacencyMatrix algebra n) where

  open CoreVectorBasedRouting algebra A
  open CoreVectorBasedRoutingProperties isRoutingAlgebra A

  h[FXᵢⱼ]⊔h[FYᵢⱼ]<v : ∀ X Y {i j v} → F X i j <₊ F Y i j →
                    (∀ k → X k j ≉ Y k j → r (X k j) (Y k j) ≤ v) →
                    h (F X i j) ⊔ h (F Y i j) < v
  h[FXᵢⱼ]⊔h[FYᵢⱼ]<v X Y {i} {j} {v} FXᵢⱼ<FYᵢⱼ@(FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) d≤v with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ...   | inj₂ FXᵢⱼ≈Iᵢⱼ = contradiction FXᵢⱼ≈Iᵢⱼ (FXᵢⱼ<FYᵢⱼ⇒FXᵢⱼ≉Iᵢⱼ X Y FXᵢⱼ<FYᵢⱼ)
  ...   | inj₁ (k , FXᵢⱼ≈AᵢₖXₖⱼ) = begin
    h (F X i j) ⊔ h (F Y i j) ≡⟨ m≤n⇒n⊔m≡n (h-resp-≤ FXᵢⱼ≤FYᵢⱼ) ⟩
    h (F X i j)               ≡⟨ h-cong FXᵢⱼ≈AᵢₖXₖⱼ ⟩
    h (A i k ▷ X k j)         <⟨ h-resp-< (isStrictlyIncreasing (A i k) Xₖⱼ≉∞) ⟩
    h (X k j)                 ≤⟨ m≤m⊔n (h (X k j)) (h (Y k j)) ⟩
    h (X k j) ⊔ h (Y k j)     ≡⟨ sym (r[x,y]≡hx⊔hy Xₖⱼ≉Yₖⱼ) ⟩
    r (X k j) (Y k j)         ≤⟨ d≤v k Xₖⱼ≉Yₖⱼ ⟩
    v                         ∎
    where

    FYᵢⱼ≰AᵢₖXₖⱼ : F Y i j ≰₊ A i k ▷ X k j
    FYᵢⱼ≰AᵢₖXₖⱼ FYᵢⱼ≤AᵢₖXₖⱼ = FXᵢⱼ≉FYᵢⱼ (≤₊-antisym FXᵢⱼ≤FYᵢⱼ (begin
      F Y i j       ≤⟨ FYᵢⱼ≤AᵢₖXₖⱼ ⟩
      A i k ▷ X k j ≈⟨ ≈-sym FXᵢⱼ≈AᵢₖXₖⱼ ⟩
      F X i j       ∎))
      where open POR ≤₊-poset

    Xₖⱼ≉∞ : X k j ≉ ∞#
    Xₖⱼ≉∞ Xₖⱼ≈∞ = FYᵢⱼ≰AᵢₖXₖⱼ (begin
      F Y i j       ≤⟨ ⊕-identityˡ _ ⟩
      ∞#            ≈⟨ ≈-sym (▷-fixedPoint (A i k)) ⟩
      A i k ▷ ∞#    ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈∞) ⟩
      A i k ▷ X k j ∎)
      where open POR ≤₊-poset

    Xₖⱼ≉Yₖⱼ : X k j ≉ Y k j
    Xₖⱼ≉Yₖⱼ Xₖⱼ≈Yₖⱼ = FYᵢⱼ≰AᵢₖXₖⱼ (begin
      F Y i j       ≤⟨ FXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k ⟩
      A i k ▷ Y k j ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈Yₖⱼ) ⟩
      A i k ▷ X k j ∎)
      where open POR ≤₊-poset

    open ≤-Reasoning

  r[FXᵢⱼ,FYᵢⱼ]<v : ∀ X Y i j → ∀ {v} → 0 < v → (∀ k → X k j ≉ Y k j → r (X k j) (Y k j) ≤ v) →
                   r (F X i j) (F Y i j) < v
  r[FXᵢⱼ,FYᵢⱼ]<v X Y i j {v} 0<v r≤v with F X i j ≟ F Y i j
  ... | yes FXᵢⱼ≈FYᵢⱼ = 0<v
  ... | no  FXᵢⱼ≉FYᵢⱼ with ≤₊-total (F X i j) (F Y i j)
  ...   | inj₁ FXᵢⱼ≤FYᵢⱼ = h[FXᵢⱼ]⊔h[FYᵢⱼ]<v X Y (FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) r≤v
  ...   | inj₂ FYᵢⱼ≤FXᵢⱼ = begin
    h (F X i j) ⊔ h (F Y i j) ≡⟨ ⊔-comm (h (F X i j)) (h (F Y i j)) ⟩
    h (F Y i j) ⊔ h (F X i j) <⟨ h[FXᵢⱼ]⊔h[FYᵢⱼ]<v Y X (FYᵢⱼ≤FXᵢⱼ , FXᵢⱼ≉FYᵢⱼ ∘ ≈-sym) (λ k Yₖⱼ≉Xₖⱼ → subst (_≤ v) (r-sym (X k j) (Y k j)) (r≤v k (Yₖⱼ≉Xₖⱼ ∘ ≈-sym))) ⟩
    v                         ∎
    where open ≤-Reasoning

--------------------------------------------------------------------------------
-- Proof for a dynamic network

module _ {n} (network : Network algebra n) where

  open DistanceVectorRouting algebra network hiding (F)
  open DistanceVectorRoutingProperties isRoutingAlgebra network

  module _ {e : Epoch} {p : Subset n} where

    private
      A : _
      A = Aₜ e p

      F : RoutingMatrix → RoutingMatrix
      F = F′ e p

    -- This lemma is a mess as can't pattern match on `i ∈? p` directly
    -- as it unfolds the adjacency matrix
    d[FXᵢ,FYᵢ]<DXY : ∀ {X Y} → WellFormed p X → WellFormed p Y →
                     Y ≉ₘ[ p ] X → ∀ i → dᶜ p i (F X i) (F Y i) < D p X Y
    d[FXᵢ,FYᵢ]<DXY {X} {Y} wfX wfY Y≉X i with Y≉ₚX⇒0<DXY p Y≉X
    ... | 0<DXY with max[t]<x 0<DXY (λ j → r[FXᵢⱼ,FYᵢⱼ]<v A X Y i j 0<DXY (λ k _ → r≤D-wf p wfX wfY k j))
    ...   | d[FXᵢ,FYᵢ]<DXY = [
        (λ i∈p → subst (_< D p X Y) (sym (Condition.accept (d {n}) (_∈? p) i∈p)) d[FXᵢ,FYᵢ]<DXY) ,
        (λ i∉p → subst (_< D p X Y) (sym (Condition.reject (d {n}) (_∈? p) i∉p)) 0<DXY)
      ] (i ∈? p)

    F-strContr : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X →
                 D p (F X) (F Y) < D p X Y
    F-strContr wfX wfY Y≉X = max[t]<x (Y≉ₚX⇒0<DXY p Y≉X) (d[FXᵢ,FYᵢ]<DXY wfX wfY Y≉X)

    F-strContrOnOrbits : ∀ {X} → WellFormed p X → (F X) ≉ₘ[ p ] X →
                          D p (F X) (F (F X)) < D p X (F X)
    F-strContrOnOrbits {X} wfX FX≉X = F-strContr wfX (F′-inactive e p X) FX≉X

    F-strContrOnFP : ∀ {X} → WellFormed p X → ∀ {X*} → F X* ≈ₘ X* → X ≉ₘ[ p ] X* →
                     D p X* (F X) < D p X* X
    F-strContrOnFP {X} wfX {X*} FX*≈X* X≉X* = begin
      D p X*     (F X) ≡⟨ D-cong p (≈ₘ-sym FX*≈X*) (≈ₘ-refl {x = F′ e p X}) ⟩
      D p (F X*) (F X) <⟨ F-strContr (X*-wf e p FX*≈X*) wfX X≉X* ⟩
      D p X*     X     ∎
      where open ≤-Reasoning

  F∥-isAMCO : AMCO F∥
  F∥-isAMCO = record
    { dᵢ                   = λ e p → d
    ; dᵢ-isQuasiSemiMetric = λ e p i → d-isQuasiSemiMetric
    ; dᵢ-bounded           = λ e p → proj₁ (d-bounded {n}) , proj₂ d-bounded
    ; F-strContrOnOrbits   = F-strContrOnOrbits
    ; F-strContrOnFP       = F-strContrOnFP
    ; F-inactive           = F′-inactive
    }
