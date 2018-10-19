open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst₂; module ≡-Reasoning)
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_; _≤_; _≥_; _<_)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; <⇒≢; <⇒≤; <⇒≱; ≤+≢⇒<; ⊔-comm; ⊔-identityʳ; ⊔-mono-≤; ⊔-mono-<; ≤-total; ≤-reflexive; ≤-refl; ≤-trans; m≤n⇒n⊔m≡n)
open import Data.Product using (∃; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Function using (_∘_)
import RoutingLib.Relation.Binary.Reasoning.PartialOrder as PO-Reasoning

open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Sorting using (Sorted)
open import RoutingLib.Data.Matrix using (SquareMatrix; Matrix; zipWith; max⁺)
open import RoutingLib.Data.Table.Properties using (max[t]<x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; m≤n⇒m≤n⊔o; n≤m×o≤m⇒n⊔o≤m; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Function.Metric using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
open import RoutingLib.Routing.Model using (AdjacencyMatrix)
open import RoutingLib.Routing.BellmanFord.ConvergenceConditions
import RoutingLib.Routing.BellmanFord.Synchronous as BellmanFord
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Properties as BellmanFordProperties
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Properties as MetricProperties
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Metrics as Metrics

module RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.StrictlyContracting
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open RoutingAlgebraProperties isRoutingAlgebra
open Metrics isRoutingAlgebra isFinite
open MetricProperties isRoutingAlgebra isFinite

open BellmanFord algebra A
open BellmanFordProperties algebra isRoutingAlgebra A

open import RoutingLib.Function.Metric ℝ𝕄ₛ
  using (_StrContrOver_; _StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)

------------------------------------------------------------------------
-- Properties of D

σXᵢⱼ≉Iᵢⱼ : ∀ X {i j} x → i ≢ j → σ X i j <₊ x → σ X i j ≉ I i j
σXᵢⱼ≉Iᵢⱼ X {i} {j} x i≢j σXᵢⱼ<x = <₊⇒≉ (begin
  σ X i j <⟨ σXᵢⱼ<x ⟩
  x       ≤⟨ ⊕-identityˡ x ⟩
  ∞       ≡⟨ sym (Iᵢⱼ≡∞ (i≢j ∘ sym)) ⟩
  I i j   ∎)
  where open PO-Reasoning ≤₊-poset

Y≉X⇒0<DXY : ∀ {X Y : RoutingMatrix} → Y ≉ₘ X → 0 < D X Y
Y≉X⇒0<DXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₘ-sym ∘ D≡0⇒X≈Y)

hσXᵢⱼ⊔σYᵢⱼ<DXY : ∀ {X Y i j} → σ X i j <₊ σ Y i j → h (σ X i j) ⊔ h (σ Y i j) < D X Y
hσXᵢⱼ⊔σYᵢⱼ<DXY {X} {Y} {i} {j} σXᵢⱼ<σYᵢⱼ@(σXᵢⱼ≤σYᵢⱼ , σXᵢⱼ≉σYᵢⱼ) with i ≟𝔽 j
... | yes i≡j = contradiction (σXᵢᵢ≈σYᵢᵢ X Y i≡j) σXᵢⱼ≉σYᵢⱼ
... | no  i≢j with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
...   | inj₂ σXᵢⱼ≈Iᵢⱼ = contradiction σXᵢⱼ≈Iᵢⱼ (σXᵢⱼ≉Iᵢⱼ X (σ Y i j) i≢j σXᵢⱼ<σYᵢⱼ)
...   | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) = begin
  h (σ X i j) ⊔ h (σ Y i j) ≡⟨ m≤n⇒n⊔m≡n (h-resp-≤ σXᵢⱼ≤σYᵢⱼ) ⟩
  h (σ X i j)               ≡⟨ h-cong σXᵢⱼ≈AᵢₖXₖⱼ ⟩
  h (A i k ▷ X k j)         <⟨ h-resp-< (isStrictlyIncreasing (A i k) Xₖⱼ≉∞) ⟩
  h (X k j)                 ≤⟨ m≤m⊔n (h (X k j)) (h (Y k j)) ⟩
  h (X k j) ⊔ h (Y k j)     ≡⟨ sym (dxy≡hx⊔hy Xₖⱼ≉Yₖⱼ) ⟩
  d (X k j) (Y k j)         ≤⟨ d≤D X Y k j ⟩
  D X Y                     ∎
  where

  σYᵢⱼ≰AᵢₖXₖⱼ : σ Y i j ≰₊ A i k ▷ X k j
  σYᵢⱼ≰AᵢₖXₖⱼ σYᵢⱼ≤AᵢₖXₖⱼ = σXᵢⱼ≉σYᵢⱼ (≤₊-antisym σXᵢⱼ≤σYᵢⱼ (begin
    σ Y i j       ≤⟨ σYᵢⱼ≤AᵢₖXₖⱼ ⟩
    A i k ▷ X k j ≈⟨ ≈-sym σXᵢⱼ≈AᵢₖXₖⱼ ⟩
    σ X i j       ∎))
    where open PO-Reasoning ≤₊-poset

  Xₖⱼ≉∞ : X k j ≉ ∞
  Xₖⱼ≉∞ Xₖⱼ≈∞ = σYᵢⱼ≰AᵢₖXₖⱼ (begin
    σ Y i j       ≤⟨ ⊕-identityˡ _ ⟩
    ∞             ≈⟨ ≈-sym (▷-fixedPoint (A i k)) ⟩
    A i k ▷ ∞     ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈∞) ⟩
    A i k ▷ X k j ∎)
    where open PO-Reasoning ≤₊-poset

  Xₖⱼ≉Yₖⱼ : X k j ≉ Y k j
  Xₖⱼ≉Yₖⱼ Xₖⱼ≈Yₖⱼ = σYᵢⱼ≰AᵢₖXₖⱼ (begin
    σ Y i j       ≤⟨ σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k ⟩
    A i k ▷ Y k j ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈Yₖⱼ) ⟩
    A i k ▷ X k j ∎)
    where open PO-Reasoning ≤₊-poset

  open ≤-Reasoning

dσXᵢⱼσYᵢⱼ<DXY : ∀ {X Y} → Y ≉ₘ X → ∀ i j → d (σ X i j) (σ Y i j) < D X Y
dσXᵢⱼσYᵢⱼ<DXY {X} {Y} Y≉X i j with σ X i j ≟ σ Y i j
... | yes σXᵢⱼ≈σYᵢⱼ = Y≉X⇒0<DXY Y≉X
... | no  σXᵢⱼ≉σYᵢⱼ with ≤₊-total (σ X i j) (σ Y i j)
...   | inj₁ σXᵢⱼ≤σYᵢⱼ = hσXᵢⱼ⊔σYᵢⱼ<DXY (σXᵢⱼ≤σYᵢⱼ , σXᵢⱼ≉σYᵢⱼ)
...   | inj₂ σYᵢⱼ≤σXᵢⱼ = begin
  h (σ X i j) ⊔ h (σ Y i j) ≡⟨ ⊔-comm (h (σ X i j)) (h (σ Y i j)) ⟩
  h (σ Y i j) ⊔ h (σ X i j) <⟨ hσXᵢⱼ⊔σYᵢⱼ<DXY (σYᵢⱼ≤σXᵢⱼ , σXᵢⱼ≉σYᵢⱼ ∘ ≈-sym) ⟩
  D Y X                     ≡⟨ D-sym Y X ⟩
  D X Y                     ∎
  where open ≤-Reasoning

σ-strContr : σ StrContrOver D
σ-strContr {X} {Y} Y≉X =
  max[t]<x (Y≉X⇒0<DXY Y≉X) (λ i →
    max[t]<x (Y≉X⇒0<DXY Y≉X) (λ j →
      dσXᵢⱼσYᵢⱼ<DXY Y≉X i j))

σ-strContrOnFP : σ StrContrOnFixedPointOver D
σ-strContrOnFP {X} {X*} σX*≈X* X≉X* = begin
  D X*     (σ X) ≡⟨ D-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σ X}) ⟩
  D (σ X*) (σ X) <⟨ σ-strContr X≉X* ⟩
  D X*     X     ∎
  where open ≤-Reasoning

σ-strContrOnOrbits : σ StrContrOnOrbitsOver D
σ-strContrOnOrbits = σ-strContr
