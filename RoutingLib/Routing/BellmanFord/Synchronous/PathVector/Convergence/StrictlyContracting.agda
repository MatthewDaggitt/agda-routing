
open import Data.Product using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≮_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties hiding (module ≤-Reasoning)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; ⊤; ⁅_⁆; ∣_∣)
open import Data.Fin.Subset.Properties using (x∈p∩q⁺; x∈⁅x⁆; ∈⊤)
open import Data.Fin.Dec using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; cong₂)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Fin.Subset using (_\\_)
open import RoutingLib.Data.Fin.Subset.Properties
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m; m<n⇒n≢0; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.Properties using (max[t]<x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
import RoutingLib.Function.Metric as Metric
import RoutingLib.Function.Metric.MaxLift as MaxLift

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Consistency as Consistency
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Properties as PathAlgebraProperties
open import RoutingLib.Routing.Model as Model using (AdjacencyMatrix)
import RoutingLib.Routing.BellmanFord.Synchronous as BellmanFord
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Properties as BellmanFordProperties
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Metrics as PathVectorMetrics
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Properties as PathVectorMetricProperties
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Properties as DistanceVectorProperties
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.StrictlyContracting as DistanceVectorStrContr

open ≤-Reasoning

module RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.StrictlyContracting
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  (A : AdjacencyMatrix algebra n)
  (1≤n : 1 ≤ n)
  where

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open Consistency algebra isPathAlgebra A
open PathAlgebraProperties isPathAlgebra

open BellmanFord algebra A 
open BellmanFord algebraᶜ Aᶜ using () renaming (σ to σᶜ)
open BellmanFordProperties algebra isPathAlgebra A
open PathVectorMetrics isPathAlgebra A
open PathVectorMetricProperties isPathAlgebra A
private module DVP = DistanceVectorProperties isRoutingAlgebraᶜ isFiniteᶜ
private module DVSC = DistanceVectorStrContr isRoutingAlgebraᶜ isFiniteᶜ (isStrictlyIncreasingᶜ isStrictlyIncreasing) Aᶜ

------------------------------------------------------------------------
-- Properties of dᵣⁱ

private

  chain₁ : ∀ X i j → 𝑰 (σ X i j) → ∃ λ k → 𝑰 (X k j) × hⁱ (σ X i j) < hⁱ (X k j) ⊔ hⁱ (σ X k j)
  chain₁ X i j σXᵢⱼⁱ with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X _ _ σXᵢⱼⁱ
  ... | k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ , Xₖⱼⁱ = k , Xₖⱼⁱ , (begin
    hⁱ (σ X i j)              ≡⟨ hⁱ-cong 1≤n σXᵢⱼ≈Aᵢₖ▷Xₖⱼ ⟩
    hⁱ (A i k ▷ X k j)        <⟨ hⁱ-decr 1≤n (𝑰-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ σXᵢⱼⁱ) ⟩
    hⁱ (X k j)                ≤⟨ m≤m⊔n (hⁱ (X k j)) (hⁱ (σ X k j)) ⟩
    hⁱ (X k j) ⊔ hⁱ (σ X k j) ∎)

  chain₂ : ∀ X i k j → hⁱ (σ X i j) < hⁱ (X k j) ⊔ hⁱ (σ X k j) → X k j ≈ σ X k j → hⁱ (σ X i j) < hⁱ (σ X k j)
  chain₂ X i k j hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ Xₖⱼ≈σXₖⱼ = begin
    hⁱ (σ X i j)                <⟨ hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ ⟩
    hⁱ (X k j)   ⊔ hⁱ (σ X k j) ≡⟨ cong (_⊔ hⁱ (σ X k j)) (hⁱ-cong 1≤n Xₖⱼ≈σXₖⱼ) ⟩
    hⁱ (σ X k j) ⊔ hⁱ (σ X k j) ≡⟨ ⊔-idem (hⁱ (σ X k j)) ⟩
    hⁱ (σ X k j)                ∎

  reduction : ∀ X {r s} →
              (∀ {u v} → X u v ≉ σ X u v → 𝑰 (X u v) ⊎ 𝑰 (σ X u v) → dᵣⁱ (X u v) (σ X u v) ≤ dᵣⁱ (X r s) (σ X r s)) →
              ∀ i j (L : Subset n) → Acc _<_ ∣ L ∣ → (∀ {l} → l ∉ L → hⁱ (σ X l j) ≤ hⁱ (σ X i j)) →
              𝑰 (σ X i j) → hⁱ (σ X i j) < hⁱ (X r s) ⊔ hⁱ (σ X r s)
  reduction X {r} {s} dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ i j L (acc rec) L-less σXᵢⱼⁱ with chain₁ X _ _ σXᵢⱼⁱ
  ... | k , Xₖⱼⁱ , hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ  with X k j ≟ σ X k j
  ...   | no  Xₖⱼ≉σXₖⱼ = <-transˡ (hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ) (dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ Xₖⱼ≉σXₖⱼ (inj₁ Xₖⱼⁱ))
  ...   | yes Xₖⱼ≈σXₖⱼ with chain₂ X i k j hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ Xₖⱼ≈σXₖⱼ | k ∈? L
  ...     | hσXᵢⱼ<hσXₖⱼ | no  k∉L = contradiction hσXᵢⱼ<hσXₖⱼ (≤⇒≯ (L-less k∉L))
  ...     | hσXᵢⱼ<hσXₖⱼ | yes k∈L = begin
    hⁱ (σ X i j)              <⟨ hσXᵢⱼ<hσXₖⱼ ⟩
    hⁱ (σ X k j)              <⟨ reduction X dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ k j (L \\ ⁅ k ⁆) (rec _ ∣L\\k∣<∣L∣) L-exclude (𝑰-cong Xₖⱼ≈σXₖⱼ Xₖⱼⁱ) ⟩
    hⁱ (X r s) ⊔ hⁱ (σ X r s) ∎

    where

    ∣L\\k∣<∣L∣ : ∣ L \\ ⁅ k ⁆ ∣ < ∣ L ∣
    ∣L\\k∣<∣L∣ = ∣p\\q∣<∣p∣ {p = L} {⁅ k ⁆} (k , x∈p∩q⁺ (k∈L , x∈⁅x⁆ k))

    L-exclude : ∀ {l} → l ∉ (L \\ ⁅ k ⁆) → hⁱ (σ X l j) ≤ hⁱ (σ X k j)
    L-exclude {l} l∉L\\k with l ≟𝔽 k
    ... | yes refl = ≤-refl
    ... | no  l≢k  = <⇒≤ (<-transʳ (L-less (i∉p\\q⇒i∉p l∉L\\k (i∉⁅j⁆ l≢k))) hσXᵢⱼ<hσXₖⱼ)



dᵣⁱ-strContrOrbits : ∀ X {r s} →
               (∀ {u v} → X u v ≉ σ X u v → 𝑰 (X u v) ⊎ 𝑰 (σ X u v) → dᵣⁱ (X u v) (σ X u v) ≤ dᵣⁱ (X r s) (σ X r s)) →
               ∀ {i j} → 𝑰 (σ X i j) ⊎ 𝑰 (σ (σ X) i j) → dᵣⁱ (σ X i j) (σ (σ X) i j) < dᵣⁱ (X r s) (σ X r s)
dᵣⁱ-strContrOrbits X {r} {s} dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ {i} {j} σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ with ≤-total (hⁱ (σ (σ X) i j)) (hⁱ (σ X i j))
...   | inj₁ σ²Xᵢⱼ≤σXᵢⱼ = begin
  hⁱ (σ X i j) ⊔ hⁱ (σ (σ X) i j) ≡⟨ m≤n⇒n⊔m≡n σ²Xᵢⱼ≤σXᵢⱼ ⟩
  hⁱ (σ X i j)                    <⟨ reduction X dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ i j ⊤ (<-wellFounded ∣ ⊤ {n = n} ∣) (λ l∉⊤ → contradiction ∈⊤ l∉⊤) (hⁱ-force-𝑰 1≤n (swap σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ) σ²Xᵢⱼ≤σXᵢⱼ) ⟩
  hⁱ (X r s)   ⊔ hⁱ (σ X r s)     ∎
...   | inj₂ σXᵢⱼ≤σ²Xᵢⱼ with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ (σ X) _ _ (hⁱ-force-𝑰 1≤n σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ σXᵢⱼ≤σ²Xᵢⱼ)
... | k , σ²Xᵢⱼ≈Aᵢₖ▷σXₖⱼ , σXₖⱼⁱ = begin
  hⁱ (σ X i j) ⊔ hⁱ (σ (σ X) i j) ≡⟨ m≤n⇒m⊔n≡n σXᵢⱼ≤σ²Xᵢⱼ ⟩
  hⁱ (σ (σ X) i j)                ≡⟨ hⁱ-cong 1≤n σ²Xᵢⱼ≈Aᵢₖ▷σXₖⱼ ⟩
  hⁱ (A i k ▷ σ X k j)            <⟨ hⁱ-decr 1≤n (𝑰-cong σ²Xᵢⱼ≈Aᵢₖ▷σXₖⱼ (hⁱ-force-𝑰 1≤n σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ σXᵢⱼ≤σ²Xᵢⱼ)) ⟩
  hⁱ (σ X k j)                    <⟨ reduction X dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ k j ⊤ (<-wellFounded ∣ ⊤ {n = n} ∣) (λ l∉⊤ → contradiction ∈⊤ l∉⊤) σXₖⱼⁱ ⟩
  hⁱ (X r s)   ⊔ hⁱ (σ X r s)     ∎





dᵣⁱ-strContrᶜ : ∀ X Y {r s} → 𝑪ₘ X →
               (∀ {u v} → X u v ≉ Y u v → 𝑰 (X u v) ⊎ 𝑰 (Y u v) → dᵣⁱ (X u v) (Y u v) ≤ dᵣⁱ (X r s) (Y r s)) →
               ∀ {i j} → 𝑰 (σ Y i j) → dᵣⁱ (σ X i j) (σ Y i j) < dᵣⁱ (X r s) (Y r s)
dᵣⁱ-strContrᶜ X Y {r} {s} Xᶜ dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ {i} {j} σYᵢⱼⁱ with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ Y _ _ σYᵢⱼⁱ
... | k , σYᵢⱼ≈Aᵢₖ▷Yₖⱼ , Yₖⱼⁱ = begin
  hⁱ (σ X i j) ⊔ hⁱ (σ Y i j) ≡⟨ m≤n⇒m⊔n≡n (<⇒≤ (h[sᶜ]<h[rⁱ] 1≤n (σ-pres-𝑪ₘ Xᶜ i j) σYᵢⱼⁱ)) ⟩
  hⁱ (σ Y i j)            ≡⟨ hⁱ-cong 1≤n σYᵢⱼ≈Aᵢₖ▷Yₖⱼ ⟩
  hⁱ (A i k ▷ Y k j)      <⟨ hⁱ-decr 1≤n (𝑰-cong σYᵢⱼ≈Aᵢₖ▷Yₖⱼ σYᵢⱼⁱ) ⟩
  hⁱ (Y k j)              ≤⟨ n≤m⊔n (hⁱ (X k j)) (hⁱ (Y k j)) ⟩
  hⁱ (X k j) ⊔ hⁱ (Y k j) ≤⟨ dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ (Yₖⱼⁱ ∘ (λ Xₖⱼ≈Yₖⱼ → 𝑪-cong Xₖⱼ≈Yₖⱼ (Xᶜ k j))) (inj₂ Yₖⱼⁱ) ⟩
  hⁱ (X r s) ⊔ hⁱ (Y r s) ∎


------------------------------------------------------------------------
-- Properties of dᵣᶜ

dᵣᶜ-strContr : ∀ {X Y r s} → X r s ≉ Y r s →
               (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) (σXᶜ : 𝑪ₘ (σ X)) (σYᶜ : 𝑪ₘ (σ Y)) →
               (∀ {u v} → X u v ≉ Y u v →
               dᵣᶜ (Xᶜ u v) (Yᶜ u v) ≤ dᵣᶜ (Xᶜ r s) (Yᶜ r s)) →
               ∀ i j → dᵣᶜ (σXᶜ i j) (σYᶜ i j) < dᵣᶜ (Xᶜ r s) (Yᶜ r s)
dᵣᶜ-strContr {X} {Y} {r} {s} Xᵣₛ≉Yᵣₛ Xᶜ Yᶜ σXᶜ σYᶜ dᵣᶜ≤dᵣᶜXᵣₛYᵣₛ i j = begin
  DV.d (toCMatrix σXᶜ i j) (toCMatrix σYᶜ i j) ≡⟨ DVP.d-cong σXᶜᵢⱼ≈σᶜX'ᵢⱼ σYᶜᵢⱼ≈σᶜY'ᵢⱼ ⟩
  DV.d (σᶜ X' i j)         (σᶜ Y' i j)         <⟨ DVSC.d-strContr Xᵣₛ≉Yᵣₛ less i j ⟩
  DV.d (X' r s)            (Y' r s)            ≡⟨⟩
  DV.d (toCMatrix Xᶜ r s)  (toCMatrix Yᶜ r s)  ∎
  where

  open ≤-Reasoning

  X' = toCMatrix Xᶜ
  Y' = toCMatrix Yᶜ

  σXᶜᵢⱼ≈σᶜX'ᵢⱼ : toCMatrix σXᶜ i j ≈ᶜ σᶜ X' i j
  σXᶜᵢⱼ≈σᶜX'ᵢⱼ = σ-toCMatrix-commute Xᶜ σXᶜ i j

  σYᶜᵢⱼ≈σᶜY'ᵢⱼ : toCMatrix σYᶜ i j ≈ᶜ σᶜ Y' i j
  σYᶜᵢⱼ≈σᶜY'ᵢⱼ = σ-toCMatrix-commute Yᶜ σYᶜ i j

  less : ∀ u v → X' u v ≉ᶜ Y' u v → DV.d (X' u v) (Y' u v) ≤ DV.d (X' r s) (Y' r s)
  less u v X'ᵤᵥ≉σX'ᵤᵥ = dᵣᶜ≤dᵣᶜXᵣₛYᵣₛ X'ᵤᵥ≉σX'ᵤᵥ

------------------------------------------------------------------------
-- Properties of dᵣ

dᵣ-strContrOrbitsⁱ : ∀ {X i j r s} →
                   (∀ u v → dᵣ (X u v) (σ X u v) ≤ Hᶜ + dᵣⁱ (X r s) (σ X r s)) →
                   dᵣ (σ X i j) (σ (σ X) i j) < Hᶜ + dᵣⁱ (X r s) (σ X r s)
dᵣ-strContrOrbitsⁱ {X} {i} {j} {r} {s} dᵣ≤Hᶜ+dᵣⁱ with σ X i j ≟ σ (σ X) i j
... | yes σXₖ≈σYₖ = s≤s z≤n
... | no  σXₖ≉σYₖ with 𝑪? (σ X i j) | 𝑪? (σ (σ X) i j)
...   | yes σXᵢⱼᶜ | yes σ²Xᵢⱼᶜ = dᵣᶜ<Hᶜ+x 1≤n σXᵢⱼᶜ σ²Xᵢⱼᶜ _
...   | no  σXᵢⱼⁱ | _          = +-monoʳ-< Hᶜ (dᵣⁱ-strContrOrbits X (dᵣ-force-dᵣⁱ 1≤n X (σ X) dᵣ≤Hᶜ+dᵣⁱ) (inj₁ σXᵢⱼⁱ))
...   | yes _     | no  σ²Xᵢⱼⁱ = +-monoʳ-< Hᶜ (dᵣⁱ-strContrOrbits X (dᵣ-force-dᵣⁱ 1≤n X (σ X) dᵣ≤Hᶜ+dᵣⁱ) (inj₂ σ²Xᵢⱼⁱ))


chain₃ : ∀ X i j k → 𝑰 (σ X i j) → σ X i j ≈ A i k ▷ X k j →
         X k j ≈ σ X k j → size (σ X k j) < size (σ X i j)
chain₃ X i j k σXᵢⱼⁱ σXᵢⱼ≈AᵢₖXₖⱼ Xₖⱼ≈σXₖⱼ
  with ≈-trans σXᵢⱼ≈AᵢₖXₖⱼ (▷-cong (A i k) Xₖⱼ≈σXₖⱼ)
... | σXᵢⱼ≈Aᵢₖ▷σXₖⱼ = begin
    size (σ X k j)         <⟨ ≤-reflexive (sizeⁱ-incr (𝑰-cong σXᵢⱼ≈Aᵢₖ▷σXₖⱼ σXᵢⱼⁱ)) ⟩
    size (A i k ▷ σ X k j) ≡⟨ sym (size-cong σXᵢⱼ≈Aᵢₖ▷σXₖⱼ) ⟩
    size (σ X i j)         ∎
    where open ≤-Reasoning


reduction₂ : ∀ X l j → 𝑰 (σ X l j) → Acc _<_ (size (σ X l j)) →
            ∃ λ k → Hᶜ < dᵣ (X k j) (σ X k j)
reduction₂ X l j σXₗⱼⁱ (acc rec) with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X _ _ σXₗⱼⁱ
... | (k , σXₗⱼ≈AᵢₖXₖⱼ , Xₖⱼⁱ) with X k j ≟ σ X k j
...   | no  Xₖⱼ≉σXₖⱼ = k , H<dᵣ 1≤n Xₖⱼ≉σXₖⱼ (inj₁ Xₖⱼⁱ)
...   | yes Xₖⱼ≈σXₖⱼ with chain₃ X l j k σXₗⱼⁱ σXₗⱼ≈AᵢₖXₖⱼ Xₖⱼ≈σXₖⱼ
...     | |σXₖⱼ|<|σXₗⱼ| = reduction₂ X k j
    (𝑰-cong Xₖⱼ≈σXₖⱼ Xₖⱼⁱ) (rec (size (σ X k j)) |σXₖⱼ|<|σXₗⱼ|)

force-Xᶜ : ∀ X → (∀ u v → dᵣ (X u v) (σ X u v) < Hᶜ) → 𝑪ₘ X
force-Xᶜ X dᵣ<H i j with 𝑪? (X i j)
... | yes Xᵢⱼᶜ = Xᵢⱼᶜ
... | no  Xᵢⱼⁱ with X i j ≟ σ X i j
...   | no  Xᵢⱼ≉σXᵢⱼ = contradiction (<⇒≤ (H<dᵣ 1≤n Xᵢⱼ≉σXᵢⱼ (inj₁ Xᵢⱼⁱ))) (<⇒≱ (dᵣ<H i j))
...   | yes Xᵢⱼ≈σXᵢⱼ with reduction₂ X i j (𝑰-cong Xᵢⱼ≈σXᵢⱼ Xᵢⱼⁱ) (<-wellFounded (size (σ X i j)))
...     | k , Hᶜ<dᵣXₖⱼσXₖⱼ = contradiction Hᶜ<dᵣXₖⱼσXₖⱼ (<⇒≯ (dᵣ<H k j))




dᵣ-strContrOrbitsᶜ : ∀ {X r s i j} → X r s ≉ σ X r s → (Xᵣₛᶜ : 𝑪 (X r s)) (σXᵣₛᶜ : 𝑪 (σ X r s)) →
                     (∀ u v → dᵣ (X u v) (σ X u v) ≤ dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ) →
                     dᵣ (σ X i j) (σ (σ X) i j) < dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ
dᵣ-strContrOrbitsᶜ {X} {r} {s} {i} {j}  Xᵣₛ≉σXᵣₛ Xᵣₛᶜ σXᵣₛᶜ dᵣ≤dᵣᶜXᵣₛσXᵣₛ with σ X i j ≟ σ (σ X) i j
... | yes σXᵢⱼ≈σ²Xᵢⱼ = n≢0⇒0<n (Xᵣₛ≉σXᵣₛ ∘ dᵣᶜ≡0⇒x≈y 1≤n Xᵣₛᶜ σXᵣₛᶜ)
... | no  σXᵢⱼ≉σ²Xᵢⱼ with force-Xᶜ X (λ u v → <-transʳ (dᵣ≤dᵣᶜXᵣₛσXᵣₛ u v) (dᵣᶜ<Hᶜ 1≤n _ _))
...   | Xᶜ with σ-pres-𝑪ₘ Xᶜ
...     | σXᶜ with σ-pres-𝑪ₘ σXᶜ
...       | σ²Xᶜ with 𝑪? (σ X i j) | 𝑪? (σ (σ X) i j)
...         | no  σXᵢⱼⁱ | _           = contradiction (σXᶜ i j) σXᵢⱼⁱ
...         | yes _     | no  σ²Xᵢⱼⁱ  = contradiction (σ²Xᶜ i j) σ²Xᵢⱼⁱ
...         | yes σXᵢⱼᶜ  | yes σ²Xᵢⱼᶜ  = begin
  dᵣᶜ σXᵢⱼᶜ σ²Xᵢⱼᶜ          ≡⟨ dᵣᶜ-cong 1≤n _ _ _ _ ≈-refl ≈-refl ⟩
  dᵣᶜ (σXᶜ i j) (σ²Xᶜ i j) <⟨ dᵣᶜ-strContr Xᵣₛ≉σXᵣₛ Xᶜ σXᶜ σXᶜ σ²Xᶜ dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ i j ⟩
  dᵣᶜ (Xᶜ r s) (σXᶜ r s)   ≡⟨ dᵣᶜ-cong 1≤n _ _ _ _ ≈-refl ≈-refl ⟩
  dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ           ∎
  where

  open ≤-Reasoning

  dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ : ∀ {u v} → X u v ≉ σ X u v → dᵣᶜ (Xᶜ u v) (σXᶜ u v) ≤ dᵣᶜ (Xᶜ r s) (σXᶜ r s)
  dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ {u} {v} Xᵤᵥ≉σXᵤᵥ = begin
    dᵣᶜ (Xᶜ u v) (σXᶜ u v) ≤⟨ dᵣᶜ≤dᵣ 1≤n Xᵤᵥ≉σXᵤᵥ _ _ ⟩
    dᵣ (X u v) (σ X u v)  ≤⟨ dᵣ≤dᵣᶜXᵣₛσXᵣₛ u v ⟩
    dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ         ≡⟨ dᵣᶜ-cong 1≤n _ _ _ _ ≈-refl ≈-refl ⟩
    dᵣᶜ (Xᶜ r s) (σXᶜ r s) ∎

dᵣ-strContrOrbits : ∀ {X r s} → X r s ≉ σ X r s →
                    (∀ u v → dᵣ (X u v) (σ X u v) ≤ dᵣ (X r s) (σ X r s)) →
                    ∀ i j → dᵣ (σ X i j) (σ (σ X) i j) < dᵣ (X r s) (σ X r s)
dᵣ-strContrOrbits {X} {r} {s} Xᵣₛ≉σXᵣₛ dᵣ≤dᵣXᵣₛσXᵣₛ i j with X r s ≟ σ X r s
... | yes Xᵣₛ≈σXᵣₛ = contradiction Xᵣₛ≈σXᵣₛ Xᵣₛ≉σXᵣₛ
... | no  _        with 𝑪? (X r s) | 𝑪? (σ X r s)
...   | yes Xᵣₛᶜ | yes σXᵣₛᶜ = dᵣ-strContrOrbitsᶜ Xᵣₛ≉σXᵣₛ Xᵣₛᶜ σXᵣₛᶜ dᵣ≤dᵣXᵣₛσXᵣₛ
...   | no  _    | _        = dᵣ-strContrOrbitsⁱ dᵣ≤dᵣXᵣₛσXᵣₛ
...   | yes _    | no  _    = dᵣ-strContrOrbitsⁱ dᵣ≤dᵣXᵣₛσXᵣₛ





-- Strictly contracting when one of the arguments is consistent


force-Yᶜ : ∀ {X Y r s} → 𝑪ₘ X →
           (Xᵣₛᶜ : 𝑪 (X r s)) (Yᵣₛᶜ : 𝑪 (Y r s)) →
           (∀ u v → dᵣ (X u v) (Y u v) ≤ dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ) →
           𝑪ₘ Y
force-Yᶜ {X} {Y} Xᶜ Xᵣₛᶜ Yᵣₛᶜ dᵣ≤dᵣᶜXᵣₛYᵣₛ i j with X i j ≟ Y i j
... | yes Xᵢⱼ≈Yᵢⱼ = 𝑪-cong Xᵢⱼ≈Yᵢⱼ (Xᶜ i j)
... | no  Xᵢⱼ≉Yᵢⱼ with 𝑪? (Y i j)
...   | yes Yᵢⱼᶜ = Yᵢⱼᶜ
...   | no  Yᵢⱼⁱ = contradiction (dᵣ≤dᵣᶜXᵣₛYᵣₛ i j) (<⇒≱ (dᵣᶜ<dᵣ 1≤n Xᵣₛᶜ Yᵣₛᶜ Xᵢⱼ≉Yᵢⱼ (inj₂ Yᵢⱼⁱ)))

dᵣ-strContrᶜᶜ : ∀ {X Y r s} → X r s ≉ Y r s → 𝑪ₘ X →
                (Xᵣₛᶜ : 𝑪 (X r s)) (Yᵣₛᶜ : 𝑪 (Y r s)) →
                (∀ u v → dᵣ (X u v) (Y u v) ≤ dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ) →
                ∀ i j → dᵣ (σ X i j) (σ Y i j) < dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ
dᵣ-strContrᶜᶜ {X} {Y} {r} {s}  Xᵣₛ≉Yᵣₛ Xᶜ Xᵣₛᶜ Yᵣₛᶜ dᵣ≤dᵣᶜXᵣₛYᵣₛ i j
  with σ X i j ≟ σ Y i j
... | yes σXᵢⱼ≈σYᵢⱼ = n≢0⇒0<n (Xᵣₛ≉Yᵣₛ ∘ dᵣᶜ≡0⇒x≈y 1≤n Xᵣₛᶜ Yᵣₛᶜ)
... | no  σXᵢⱼ≉σYᵢⱼ with force-Yᶜ Xᶜ Xᵣₛᶜ Yᵣₛᶜ dᵣ≤dᵣᶜXᵣₛYᵣₛ
...   | Yᶜ with σ-pres-𝑪ₘ Xᶜ |  σ-pres-𝑪ₘ Yᶜ
...       | σXᶜ | σYᶜ with 𝑪? (σ X i j) | 𝑪? (σ Y i j)
...         | no  σXᵢⱼⁱ | _         = contradiction (σXᶜ i j) σXᵢⱼⁱ
...         | yes _     | no  σYᵢⱼⁱ = contradiction (σYᶜ i j) σYᵢⱼⁱ
...         | yes σXᵢⱼᶜ | yes σYᵢⱼᶜ = begin
  dᵣᶜ σXᵢⱼᶜ σYᵢⱼᶜ         ≡⟨ dᵣᶜ-cong 1≤n _ _ _ _ ≈-refl ≈-refl ⟩
  dᵣᶜ (σXᶜ i j) (σYᶜ i j) <⟨ dᵣᶜ-strContr Xᵣₛ≉Yᵣₛ Xᶜ Yᶜ σXᶜ σYᶜ dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ i j ⟩
  dᵣᶜ (Xᶜ r s) (Yᶜ r s)   ≡⟨ dᵣᶜ-cong 1≤n _ _ _ _ ≈-refl ≈-refl ⟩
  dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ           ∎
  where

  open ≤-Reasoning

  dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ : ∀ {u v} → X u v ≉ Y u v →
                   dᵣᶜ (Xᶜ u v) (Yᶜ u v) ≤ dᵣᶜ (Xᶜ r s) (Yᶜ r s)
  dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ {u} {v} Xᵤᵥ≉Yᵤᵥ = begin
    dᵣᶜ (Xᶜ u v) (Yᶜ u v) ≤⟨ dᵣᶜ≤dᵣ 1≤n Xᵤᵥ≉Yᵤᵥ _ _ ⟩
    dᵣ  (X u v)  (Y u v)  ≤⟨ dᵣ≤dᵣᶜXᵣₛYᵣₛ u v ⟩
    dᵣᶜ Xᵣₛᶜ     Yᵣₛᶜ     ≡⟨ dᵣᶜ-cong 1≤n _ _ _ _ ≈-refl ≈-refl ⟩
    dᵣᶜ (Xᶜ r s) (Yᶜ r s) ∎

dᵣ-strContrᶜⁱ : ∀ {X Y : RoutingMatrix} {r s} → 𝑪ₘ X → 𝑰 (Y r s) →
                (∀ u v → dᵣ (X u v) (Y u v) ≤ Hᶜ + dᵣⁱ (X r s) (Y r s)) →
                ∀ i j → dᵣ (σ X i j) (σ Y i j) < Hᶜ + dᵣⁱ (X r s) (Y r s)
dᵣ-strContrᶜⁱ {X} {Y} {r} {s} Xᶜ Yᵣₛⁱ dᵣ≤Hᶜ+dᵣⁱ i j with σ X i j ≟ σ Y i j
... | yes σXᵢⱼ≈σYᵢⱼ = s≤s z≤n
... | no  σXᵢⱼ≉σYᵢⱼ with 𝑪? (σ X i j) | 𝑪? (σ Y i j)
...   | yes σXᵢⱼᶜ | yes σYᵢⱼᶜ = dᵣᶜ<Hᶜ+x 1≤n σXᵢⱼᶜ σYᵢⱼᶜ _
...   | yes _     | no  σYᵢⱼⁱ = +-monoʳ-< Hᶜ (dᵣⁱ-strContrᶜ X Y Xᶜ (dᵣ-force-dᵣⁱ 1≤n X Y dᵣ≤Hᶜ+dᵣⁱ) σYᵢⱼⁱ)
...   | no  σXᵢⱼⁱ | _         = contradiction (σ-pres-𝑪ₘ Xᶜ i j) σXᵢⱼⁱ

  --(dᵣⁱ-strContrOrbits X (dᵣ-force-dᵣⁱ X dᵣ≤Hᶜ+dᵣⁱ) (inj₂ σ²Xᵢⱼⁱ))

dᵣ-strContrᶜ : ∀ {X Y r s} → 𝑪ₘ X → X r s ≉ Y r s →
              (∀ u v → dᵣ (X u v) (Y u v) ≤ dᵣ (X r s) (Y r s)) →
              ∀ i j → dᵣ (σ X i j) (σ Y i j) < dᵣ (X r s) (Y r s)
dᵣ-strContrᶜ {X} {Y} {r} {s} Xᶜ Xᵣₛ≉Yᵣₛ dᵣ≤dᵣXᵣₛYᵣₛ with X r s ≟ Y r s
... | yes Xᵣₛ≈Yᵣₛ = contradiction Xᵣₛ≈Yᵣₛ Xᵣₛ≉Yᵣₛ
... | no  _        with 𝑪? (X r s) | 𝑪? (Y r s)
...   | yes Xᵣₛᶜ | yes Yᵣₛᶜ = dᵣ-strContrᶜᶜ Xᵣₛ≉Yᵣₛ Xᶜ Xᵣₛᶜ Yᵣₛᶜ dᵣ≤dᵣXᵣₛYᵣₛ
...   | yes _    | no  Yᵣₛⁱ = dᵣ-strContrᶜⁱ Xᶜ Yᵣₛⁱ dᵣ≤dᵣXᵣₛYᵣₛ
...   | no  Xᵣₛⁱ | _        = contradiction (Xᶜ r s) Xᵣₛⁱ


------------------------------------------------------------------------
-- Properties of dᵣ


-- Strictly contracting

open Metric ℝ𝕄ₛ using (_StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)

σ-strContrOrbits : σ StrContrOnOrbitsOver D
σ-strContrOrbits {X} σX≉X with max[t]∈t 0 (λ i → dₜ (X i) (σ X i))
... | inj₁ dXσX≡0              = contradiction (≈ₘ-sym (D≡0⇒X≈Y 1≤n dXσX≡0)) σX≉X
... | inj₂ (r , DXσX≡dₜXᵣσXᵣ) with max[t]∈t 0 (λ i → dᵣ (X r i) (σ X r i))
...   | inj₁ dXᵣσXᵣ≡0               = contradiction (≈ₘ-sym (D≡0⇒X≈Y 1≤n (trans DXσX≡dₜXᵣσXᵣ dXᵣσXᵣ≡0))) σX≉X
...   | inj₂ (s , dXᵣσXᵣ≡dᵣXᵣₛσXᵣₛ) = begin
  D (σ X) (σ (σ X))   <⟨ test ⟩
  dᵣ (X r s) (σ X r s) ≡⟨ sym DXσX≈dᵣXᵣₛσXᵣₛ ⟩
  D X (σ X)            ∎
  where
  open ≤-Reasoning

  DXσX≈dᵣXᵣₛσXᵣₛ : D X (σ X) ≡ dᵣ (X r s) (σ X r s)
  DXσX≈dᵣXᵣₛσXᵣₛ = trans DXσX≡dₜXᵣσXᵣ dXᵣσXᵣ≡dᵣXᵣₛσXᵣₛ

  Xᵣₛ≉σXᵣₛ : X r s ≉ σ X r s
  Xᵣₛ≉σXᵣₛ Xᵣₛ≈σXᵣₛ = σX≉X (≈ₘ-sym (D≡0⇒X≈Y 1≤n (trans DXσX≈dᵣXᵣₛσXᵣₛ (x≈y⇒dᵣ≡0 1≤n Xᵣₛ≈σXᵣₛ))))

  dᵣ≤dᵣXᵣₛσXᵣₛ : ∀ u v → dᵣ (X u v) (σ X u v) ≤ dᵣ (X r s) (σ X r s)
  dᵣ≤dᵣXᵣₛσXᵣₛ u v = begin
    dᵣ (X u v) (σ X u v)  ≤⟨ MaxLift.dᵢ≤d ℝ𝕋ₛⁱ dᵣ (X u) (σ X u) v ⟩
    dₜ (X u)   (σ X u)   ≤⟨ MaxLift.dᵢ≤d ℝ𝕄ₛⁱ dₜ X (σ X) u ⟩
    D X (σ X)            ≡⟨ DXσX≈dᵣXᵣₛσXᵣₛ ⟩
    dᵣ (X r s) (σ X r s) ∎

  0<dᵣXᵣₛσXᵣₛ : 0 < dᵣ (X r s) (σ X r s)
  0<dᵣXᵣₛσXᵣₛ = n≢0⇒0<n (Xᵣₛ≉σXᵣₛ ∘ dᵣ≡0⇒x≈y 1≤n)

  test : D (σ X) (σ (σ X)) < dᵣ (X r s) (σ X r s)
  test = max[t]<x 0<dᵣXᵣₛσXᵣₛ (λ i →
           max[t]<x 0<dᵣXᵣₛσXᵣₛ (λ j →
             dᵣ-strContrOrbits Xᵣₛ≉σXᵣₛ dᵣ≤dᵣXᵣₛσXᵣₛ i j))




-- Strictly contracting when one of the arguments is consistent

σ-strContrᶜ : ∀ {X Y} → 𝑪ₘ X → X ≉ₘ Y → D (σ X) (σ Y) < D X Y
σ-strContrᶜ {X} {Y} Xᶜ X≉Y with max[t]∈t 0 (λ i → dₜ (X i) (Y i))
... | inj₁ dXY≡0              = contradiction (D≡0⇒X≈Y 1≤n dXY≡0) X≉Y
... | inj₂ (r , DXY≡dₜXᵣYᵣ) with max[t]∈t 0 (λ i → dᵣ (X r i) (Y r i))
...   | inj₁ dXᵣYᵣ≡0               = contradiction (D≡0⇒X≈Y 1≤n (trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡0)) X≉Y
...   | inj₂ (s , dXᵣYᵣ≡dᵣXᵣₛYᵣₛ) = begin
  D  (σ X)   (σ Y)   <⟨ test ⟩
  dᵣ (X r s) (Y r s) ≡⟨ sym DXY≈dᵣXᵣₛYᵣₛ ⟩
  D  X       Y       ∎
  where
  open ≤-Reasoning

  DXY≈dᵣXᵣₛYᵣₛ : D X Y ≡ dᵣ (X r s) (Y r s)
  DXY≈dᵣXᵣₛYᵣₛ = trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡dᵣXᵣₛYᵣₛ

  Xᵣₛ≉Yᵣₛ : X r s ≉ Y r s
  Xᵣₛ≉Yᵣₛ Xᵣₛ≈Yᵣₛ = X≉Y (D≡0⇒X≈Y 1≤n (trans DXY≈dᵣXᵣₛYᵣₛ (x≈y⇒dᵣ≡0 1≤n Xᵣₛ≈Yᵣₛ)))

  dᵣ≤dᵣXᵣₛYᵣₛ : ∀ u v → dᵣ (X u v) (Y u v) ≤ dᵣ (X r s) (Y r s)
  dᵣ≤dᵣXᵣₛYᵣₛ u v = begin
    dᵣ (X u v) (Y u v) ≤⟨ MaxLift.dᵢ≤d ℝ𝕋ₛⁱ dᵣ (X u) (Y u) v ⟩
    dₜ (X u)   (Y u)   ≤⟨ MaxLift.dᵢ≤d ℝ𝕄ₛⁱ dₜ X (Y) u ⟩
    D X (Y)           ≡⟨ DXY≈dᵣXᵣₛYᵣₛ ⟩
    dᵣ (X r s) (Y r s) ∎

  0<dᵣXᵣₛYᵣₛ : 0 < dᵣ (X r s) (Y r s)
  0<dᵣXᵣₛYᵣₛ = n≢0⇒0<n (Xᵣₛ≉Yᵣₛ ∘ dᵣ≡0⇒x≈y 1≤n)

  test : D (σ X) (σ Y) < dᵣ (X r s) (Y r s)
  test = max[t]<x 0<dᵣXᵣₛYᵣₛ (λ i →
           max[t]<x 0<dᵣXᵣₛYᵣₛ (λ j →
             dᵣ-strContrᶜ Xᶜ Xᵣₛ≉Yᵣₛ dᵣ≤dᵣXᵣₛYᵣₛ i j))


σ-strContrOnFP : σ StrContrOnFixedPointOver D
σ-strContrOnFP {X} {X*} σX*≈X* X≉X* = begin
  D X*     (σ X) ≡⟨ D-cong 1≤n (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σ X}) ⟩
  D (σ X*) (σ X) <⟨ σ-strContrᶜ (fixedPointᶜ σX*≈X*) (X≉X* ∘ ≈ₘ-sym) ⟩
  D X*     X     ∎
  where open ≤-Reasoning
