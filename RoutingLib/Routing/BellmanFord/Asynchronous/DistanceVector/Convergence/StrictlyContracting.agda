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
import RoutingLib.Function.Metric.SubsetMaxLift as SubsetMaxLift
import RoutingLib.Function.Metric as Metric
import RoutingLib.Relation.Binary.Reasoning.PartialOrder as PO-Reasoning

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
open import RoutingLib.Routing.Model using (AdjacencyMatrix)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Properties as SyncBellmanFordProperties
import RoutingLib.Routing.BellmanFord.Asynchronous as AsyncBellmanFord
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Metrics as SyncMetrics
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Properties as SyncMetricProperties

module RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Convergence.Metrics
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  {n} (network : Epoch → AdjacencyMatrix algebra n)
  
  where

open AsyncBellmanFord algebra network hiding (AdjacencyMatrix)
open SyncMetrics isRoutingAlgebra isFinite renaming (H to dₘₐₓ)
open SyncMetricProperties isRoutingAlgebra isFinite
  
module _ (e : Epoch) (p : Subset n) where

  F : RoutingMatrix → RoutingMatrix
  F = Fₜ e p

  A : AdjacencyMatrix algebra n
  A = Aₜ e p

  open IsRoutingAlgebra isRoutingAlgebra
  open RawRoutingAlgebra algebra
  open RoutingAlgebraProperties isRoutingAlgebra
  open SyncBellmanFordProperties algebra isRoutingAlgebra A

  cond : ∀ {i : Fin n} → RoutingTable → RoutingTable → ℕ
  cond {i} = SubsetMaxLift.cond ℝ𝕄ₛⁱ dₜ p {i}

  Dˢ : RoutingMatrix → RoutingMatrix → ℕ
  Dˢ = SubsetMaxLift.dˢ ℝ𝕄ₛⁱ dₜ p

  Dˢ-sym : ∀ X Y → Dˢ X Y ≡ Dˢ Y X
  Dˢ-sym = SubsetMaxLift.dˢ-sym ℝ𝕄ₛⁱ dₜ p dₜ-sym

  Dˢ-cong : Dˢ Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
  Dˢ-cong = SubsetMaxLift.dˢ-cong ℝ𝕄ₛⁱ dₜ p dₜ-cong

  Dˢ-congˢ : Dˢ Preserves₂ (_≈ₘ[ p ]_) ⟶ (_≈ₘ[ p ]_) ⟶ _≡_
  Dˢ-congˢ = SubsetMaxLift.dˢ-congˢ ℝ𝕄ₛⁱ dₜ p dₜ-cong
  
  dₜ≤Dˢ : ∀ X Y i → (i ∈ p ⊎ X i ≈ₜ Y i) → dₜ (X i) (Y i) ≤ Dˢ X Y
  dₜ≤Dˢ X Y i (inj₁ i∈p)  = SubsetMaxLift.dᵢ≤dˢ ℝ𝕄ₛⁱ dₜ p X Y i∈p
  dₜ≤Dˢ X Y i (inj₂ Xᵢ≈Yᵢ) = x≤max[t] 0 (λ i → cond (X i) (Y i)) (inj₁ (≤-reflexive (x≈y⇒dₜ≡0 Xᵢ≈Yᵢ)))

  d≤Dˢ : ∀ X Y i j → (i ∈ p ⊎ X i ≈ₜ Y i) → d (X i j) (Y i j) ≤ Dˢ X Y
  d≤Dˢ X Y i j op = ≤-trans (d≤dₜ (X i) (Y i) j) (dₜ≤Dˢ X Y i op)

  d≤Dˢ-wf : ∀ {X Y} → WellFormed p X → WellFormed p Y → ∀ i j → d (X i j) (Y i j) ≤ Dˢ X Y
  d≤Dˢ-wf {X} {Y} wfX wfY i j with i ∈? p
  ... | yes i∈p = d≤Dˢ X Y i j (inj₁ i∈p)
  ... | no  i∉p = d≤Dˢ X Y i j (inj₂ (WellFormed-cong wfX wfY i∉p))

  Y≉ₚX⇒0<DˢXY : ∀ {X Y} → Y ≉ₘ[ p ]  X → 0 < Dˢ X Y
  Y≉ₚX⇒0<DˢXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₛ-sym ∘ SubsetMaxLift.dˢ≡0⇒x≈ₛy ℝ𝕄ₛⁱ dₜ p dₜ≡0⇒x≈y)


  FXᵢⱼ≉Iᵢⱼ : ∀ X {i j} x → i ≢ j → F X i j <₊ x → F X i j ≉ I i j
  FXᵢⱼ≉Iᵢⱼ X {i} {j} x i≢j FXᵢⱼ<x = <₊⇒≉ (begin
    F X i j <⟨ FXᵢⱼ<x ⟩
    x       ≤⟨ ⊕-identityˡ x ⟩
    ∞       ≡⟨ sym (Iᵢⱼ≡∞ (i≢j ∘ sym)) ⟩
    I i j   ∎)
    where open PO-Reasoning ≤₊-poset

  hFXᵢⱼ⊔FYᵢⱼ<DXY : ∀ {X Y i j} → F X i j <₊ F Y i j →
                  (∀ k → d (X k j) (Y k j) ≤ Dˢ X Y) →
                  h (F X i j) ⊔ h (F Y i j) < Dˢ X Y
  hFXᵢⱼ⊔FYᵢⱼ<DXY {X} {Y} {i} {j} FXᵢⱼ<FYᵢⱼ@(FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) d≤Dˢ with i ≟𝔽 j
  ... | yes i≡j = contradiction (σXᵢᵢ≈σYᵢᵢ X Y i≡j) FXᵢⱼ≉FYᵢⱼ
  ... | no  i≢j with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ...   | inj₂ FXᵢⱼ≈Iᵢⱼ = contradiction FXᵢⱼ≈Iᵢⱼ (FXᵢⱼ≉Iᵢⱼ X (F Y i j) i≢j FXᵢⱼ<FYᵢⱼ)
  ...   | inj₁ (k , FXᵢⱼ≈AᵢₖXₖⱼ) = begin
    h (F X i j) ⊔ h (F Y i j)  ≡⟨ m≤n⇒n⊔m≡n (h-resp-≤ FXᵢⱼ≤FYᵢⱼ) ⟩
    h (F X i j)                ≡⟨ h-cong FXᵢⱼ≈AᵢₖXₖⱼ ⟩
    h (A i k ▷ X k j)          <⟨ h-resp-< (isStrictlyIncreasing (A i k) Xₖⱼ≉∞) ⟩
    h (X k j)                  ≤⟨ m≤m⊔n (h (X k j)) (h (Y k j)) ⟩
    h (X k j) ⊔ h (Y k j)      ≡⟨ sym (dxy≡hx⊔hy Xₖⱼ≉Yₖⱼ) ⟩
    d (X k j) (Y k j)          ≤⟨ d≤Dˢ k ⟩
    Dˢ X Y                     ∎
    where

    FYᵢⱼ≰AᵢₖXₖⱼ : F Y i j ≰₊ A i k ▷ X k j
    FYᵢⱼ≰AᵢₖXₖⱼ FYᵢⱼ≤AᵢₖXₖⱼ = FXᵢⱼ≉FYᵢⱼ (≤₊-antisym FXᵢⱼ≤FYᵢⱼ (begin
      F Y i j        ≤⟨ FYᵢⱼ≤AᵢₖXₖⱼ ⟩
      A i k ▷ X k j  ≈⟨ ≈-sym FXᵢⱼ≈AᵢₖXₖⱼ ⟩
      F X i j        ∎))
      where open PO-Reasoning ≤₊-poset

    Xₖⱼ≉∞ : X k j ≉ ∞
    Xₖⱼ≉∞ Xₖⱼ≈∞ = FYᵢⱼ≰AᵢₖXₖⱼ (begin
      F Y i j       ≤⟨ ⊕-identityˡ _ ⟩
      ∞             ≈⟨ ≈-sym (▷-fixedPoint (A i k)) ⟩
      A i k ▷ ∞     ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈∞) ⟩
      A i k ▷ X k j ∎)
      where open PO-Reasoning ≤₊-poset

    Xₖⱼ≉Yₖⱼ : X k j ≉ Y k j
    Xₖⱼ≉Yₖⱼ Xₖⱼ≈Yₖⱼ = FYᵢⱼ≰AᵢₖXₖⱼ (begin
      F Y i j       ≤⟨ σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k ⟩
      A i k ▷ Y k j ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈Yₖⱼ) ⟩
      A i k ▷ X k j ∎)
      where open PO-Reasoning ≤₊-poset

    open ≤-Reasoning


  dFXᵢⱼFYᵢⱼ<DXY : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X →
                 ∀ i j → d (F X i j) (F Y i j) < Dˢ X Y
  dFXᵢⱼFYᵢⱼ<DXY {X} {Y} wfX wfY Y≉X i j with F X i j ≟ F Y i j
  ... | yes FXᵢⱼ≈FYᵢⱼ = Y≉ₚX⇒0<DˢXY Y≉X
  ... | no  FXᵢⱼ≉FYᵢⱼ with ≤₊-total (F X i j) (F Y i j)
  ...   | inj₁ FXᵢⱼ≤FYᵢⱼ = hFXᵢⱼ⊔FYᵢⱼ<DXY (FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) (λ k → d≤Dˢ-wf wfX wfY k j)
  ...   | inj₂ FYᵢⱼ≤FXᵢⱼ = begin
    h (F X i j) ⊔ h (F Y i j) ≡⟨ ⊔-comm (h (F X i j)) (h (F Y i j)) ⟩
    h (F Y i j) ⊔ h (F X i j) <⟨ hFXᵢⱼ⊔FYᵢⱼ<DXY (FYᵢⱼ≤FXᵢⱼ , FXᵢⱼ≉FYᵢⱼ ∘ ≈-sym) (λ k → d≤Dˢ-wf wfY wfX k j) ⟩
    Dˢ Y X                    ≡⟨ Dˢ-sym Y X ⟩
    Dˢ X Y                    ∎
    where open ≤-Reasoning

  dₜFXᵢFYᵢ<DˢXY : ∀ {X Y} → WellFormed p X → WellFormed p Y →
                 Y ≉ₘ[ p ] X → ∀ i → cond {i} (F X i) (F Y i) < Dˢ X Y
  dₜFXᵢFYᵢ<DˢXY wfX wfY Y≉X i with i ∈? p
  ... | no  _ = Y≉ₚX⇒0<DˢXY Y≉X
  ... | yes _ = max[t]<x (Y≉ₚX⇒0<DˢXY Y≉X) (dFXᵢⱼFYᵢⱼ<DXY wfX wfY Y≉X i)

  Dˢ-strContr-F : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X →
                  Dˢ (F X) (F Y) < Dˢ X Y
  Dˢ-strContr-F wfX wfY Y≉X = max[t]<x (Y≉ₚX⇒0<DˢXY Y≉X) (dₜFXᵢFYᵢ<DˢXY wfX wfY Y≉X)

  X*-wf : ∀ {X*} → F X* ≈ₘ X* → WellFormed p X*
  X*-wf {X*} FX*≈X* {i} i∉p = ≈ₜ-trans (≈ₘ-sym FX*≈X* i) (Fₜ-inactive e X* i∉p)
  
F-strContrOnOrbits : ∀ e p {X} → WellFormed p X → (Fₜ e p X) ≉ₘ[ p ] X →
                      Dˢ e p (Fₜ e p X) (Fₜ e p (Fₜ e p X)) < Dˢ e p X (Fₜ e p X)
F-strContrOnOrbits e p {X} wfX FX≉X = Dˢ-strContr-F e p wfX (Fₜ-inactive e X) FX≉X

F-strContrOnFP : ∀ e p {X} → WellFormed p X → ∀ {X*} → Fₜ e p X* ≈ₘ X* → X ≉ₘ[ p ] X* →
                 Dˢ e p X* (Fₜ e p X) < Dˢ e p X* X
F-strContrOnFP e p {X} wfX {X*} FX*≈X* X≉X* = begin
  Dˢ e p X*          (Fₜ e p X) ≡⟨ Dˢ-cong e p (≈ₘ-sym FX*≈X*) (≈ₘ-refl {x = Fₜ e p X}) ⟩
  Dˢ e p (Fₜ e p X*) (Fₜ e p X) <⟨ Dˢ-strContr-F e p (X*-wf e p FX*≈X*) wfX X≉X* ⟩
  Dˢ e p X*          X          ∎
  where open ≤-Reasoning
  

ultrametricConditions : UltrametricConditions σ∥
ultrametricConditions = record
  { dᵢ                 = dₜ
  ; dᵢ-cong            = dₜ-cong
  ; x≈y⇒dᵢ≡0           = x≈y⇒dₜ≡0
  ; dᵢ≡0⇒x≈y           = dₜ≡0⇒x≈y
  ; dᵢ-bounded         = {!!} --dₘₐₓ , proj₂ (dₜ-bounded n)
  ; element            = I
  ; F-strContrOnOrbits = F-strContrOnOrbits
  ; F-strContrOnFP     = F-strContrOnFP
  }
