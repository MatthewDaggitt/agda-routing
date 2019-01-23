open import Data.Product using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≮_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties hiding (module ≤-Reasoning; _≟_)
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
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.Properties using (max[t]<x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
import RoutingLib.Function.Metric as Metric
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift

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
open PathVectorMetricProperties isPathAlgebra A 1≤n
private module DVP = DistanceVectorProperties isRoutingAlgebraᶜ isFiniteᶜ
private module DVSC = DistanceVectorStrContr isRoutingAlgebraᶜ isFiniteᶜ (isStrictlyIncreasingᶜ isStrictlyIncreasing) Aᶜ

------------------------------------------------------------------------
-- rᶜ is contracting in the right way

rᶜ-strContr-𝑪𝑪 : ∀ {X Y} → (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) →
                 ∀ {i j} (σXᵢⱼᶜ : 𝑪 (σ X i j)) (σYᵢⱼᶜ : 𝑪 (σ Y i j)) →
                 ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                 rᶜ σXᵢⱼᶜ σYᵢⱼᶜ < v
rᶜ-strContr-𝑪𝑪 {X} {Y} Xᶜ Yᶜ {i} {j} σXᵢⱼᶜ σYᵢⱼᶜ {v} 0<v r≤v = begin
  rᶜ σXᵢⱼᶜ σYᵢⱼᶜ                        ≡⟨⟩
  DV.r (toCRoute σXᵢⱼᶜ) (toCRoute σYᵢⱼᶜ) ≡⟨ DVP.d-cong {n} ≈-refl ≈-refl ⟩
  DV.r (cσX i j) (cσY i j)               ≡⟨ DVP.d-cong {n} (σ-toCMatrix-commute Xᶜ (σ-pres-𝑪ₘ Xᶜ) i j) (σ-toCMatrix-commute Yᶜ (σ-pres-𝑪ₘ Yᶜ) i j) ⟩
  DV.r (σᶜ cX i j) (σᶜ cY i j)           <⟨ DVSC.r[σXᵢⱼ,σYᵢⱼ]<v cX cY i j 0<v d≤v ⟩
  v                                      ∎
  where
  cX  = toCMatrix Xᶜ
  cσX = toCMatrix (σ-pres-𝑪ₘ Xᶜ)
  cY  = toCMatrix Yᶜ
  cσY = toCMatrix (σ-pres-𝑪ₘ Yᶜ)
  d≤v : ∀ k → cX k j ≉ᶜ cY k j → DV.r (cX k j) (cY k j) ≤ v
  d≤v k cXₖⱼ≉cYₖⱼ = begin
    DV.r (cX k j) (cY k j) ≡⟨⟩
    rᶜ  (Xᶜ k j) (Yᶜ k j) ≡⟨ rᶜ≡r (Xᶜ k j) (Yᶜ k j) ≈-refl ≈-refl cXₖⱼ≉cYₖⱼ ⟩
    r   (X k j)  (Y k j)  ≤⟨ r≤v k j ⟩
    v                      ∎
    where open ≤-Reasoning

rᶜ-strContr-𝑪𝑰 : ∀ {X Y i j} → (𝑰ₘ X × 𝑪ₘ Y) ⊎ (𝑪ₘ X × 𝑰ₘ Y) →
                 (σXᵢⱼᶜ : 𝑪 (σ X i j)) (σYᵢⱼᶜ : 𝑪 (σ Y i j)) →
                 ∀ {v} → (∀ k l → r (X k l) (Y k l) ≤ v) →
                 rᶜ σXᵢⱼᶜ σYᵢⱼᶜ < v
rᶜ-strContr-𝑪𝑰 {X} {Y} (inj₁ (Xⁱ , Yᶜ)) σXᵢⱼᶜ σYᵢⱼᶜ {v} r≤v with 𝑰ₘ-witness Xⁱ
...   | (k , l , Xₖₗⁱ) = begin
  rᶜ σXᵢⱼᶜ  σYᵢⱼᶜ         <⟨ rᶜ<Hᶜ+x σXᵢⱼᶜ σYᵢⱼᶜ _ ⟩
  Hᶜ + rⁱ (X k l) (Y k l) ≡⟨ H+rⁱ≡r ≈-refl ≈-refl (𝑪𝑰⇒≉ (Yᶜ k l) Xₖₗⁱ ∘ ≈-sym) (inj₁ Xₖₗⁱ) ⟩
  r (X k l) (Y k l)       ≤⟨ r≤v k l ⟩
  v                        ∎
  where open ≤-Reasoning
rᶜ-strContr-𝑪𝑰 {X} {Y} (inj₂ (Xᶜ , Yⁱ)) σXᵢⱼᶜ σYᵢⱼᶜ {v} r≤v with 𝑰ₘ-witness Yⁱ
... | (k , l , Yₖₗⁱ) = begin
  rᶜ σXᵢⱼᶜ  σYᵢⱼᶜ           <⟨ rᶜ<Hᶜ+x σXᵢⱼᶜ σYᵢⱼᶜ _ ⟩
  Hᶜ + rⁱ (X k l) (Y k l) ≡⟨ H+rⁱ≡r ≈-refl ≈-refl (𝑪𝑰⇒≉ (Xᶜ k l) Yₖₗⁱ) (inj₂ Yₖₗⁱ) ⟩
  r (X k l) (Y k l)       ≤⟨ r≤v k l ⟩
  v                        ∎
  where open ≤-Reasoning

rᶜ-strContrOrbits : ∀ {X i j} →
                     (σXᵢⱼᶜ : 𝑪 (σ X i j)) (σ²Xᵢⱼᶜ : 𝑪 (σ (σ X) i j)) →
                     ∀ {v} → 0 < v → (∀ k l → r (X k l) (σ X k l) ≤ v) →
                     rᶜ σXᵢⱼᶜ σ²Xᵢⱼᶜ < v
rᶜ-strContrOrbits {X} {i} {j} σXᵢⱼᶜ σ²Xᵢⱼᶜ {v} 0<v r≤v with 𝑪ₘ? X | 𝑪ₘ? (σ X)
... | yes Xᶜ | yes σXᶜ = rᶜ-strContr-𝑪𝑪 Xᶜ σXᶜ σXᵢⱼᶜ σ²Xᵢⱼᶜ 0<v r≤v
... | yes Xᶜ | no  σXⁱ = contradiction (σ-pres-𝑪ₘ Xᶜ) σXⁱ
... | no  Xⁱ | yes σXᶜ = rᶜ-strContr-𝑪𝑰 (inj₁ (Xⁱ , σXᶜ)) σXᵢⱼᶜ σ²Xᵢⱼᶜ r≤v
... | no  Xⁱ | no  σXⁱ with 𝑰ₘ-witness σXⁱ
...   | (m , n , σXₘₙⁱ) with σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ X m n σXₘₙⁱ
...     | (k , Xₖₙ≉σXₖₙ , Xₖₙⁱ , _) = begin
  rᶜ σXᵢⱼᶜ  σ²Xᵢⱼᶜ            <⟨ rᶜ<Hᶜ+x σXᵢⱼᶜ σ²Xᵢⱼᶜ _ ⟩
  Hᶜ + rⁱ (X k n) (σ X k n) ≡⟨ H+rⁱ≡r ≈-refl ≈-refl Xₖₙ≉σXₖₙ (inj₁ Xₖₙⁱ) ⟩
  r (X k n) (σ X k n)       ≤⟨ r≤v k n ⟩
  v                          ∎
  where open ≤-Reasoning

rᶜ-strContrOn𝑪 : ∀ {X Y} → 𝑪ₘ X →
                  ∀ {i j} → (σXᵢⱼᶜ : 𝑪 (σ X i j)) (σYᵢⱼᶜ : 𝑪 (σ Y i j)) →
                  ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                  rᶜ σXᵢⱼᶜ σYᵢⱼᶜ < v
rᶜ-strContrOn𝑪 {X} {Y} Xᶜ {i} {j} σXᵢⱼᶜ σYᵢⱼᶜ 0<v r≤v with 𝑪ₘ? Y
... | yes Yᶜ = rᶜ-strContr-𝑪𝑪 Xᶜ Yᶜ σXᵢⱼᶜ σYᵢⱼᶜ 0<v r≤v
... | no  Yⁱ = rᶜ-strContr-𝑪𝑰 (inj₂ (Xᶜ , Yⁱ)) σXᵢⱼᶜ σYᵢⱼᶜ r≤v

------------------------------------------------------------------------
-- rⁱ is contracting in the right way

rⁱ-strContrOrbits-σX : ∀ {X i j} → 𝑰 (σ X i j) →
                        ∀ {v} → (∀ k l → r (X k l) (σ X k l) ≤ v) →
                        Hᶜ + hⁱ (σ X i j) < v
rⁱ-strContrOrbits-σX {X} {i} {j} σXᵢⱼⁱ {v} r≤v with σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ X i j σXᵢⱼⁱ
... | (k , Xₖⱼ≉σXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|σXᵢⱼ|) = begin
  Hᶜ + hⁱ (σ X i j)                 <⟨ +-monoʳ-< Hᶜ (hⁱ-mono Xₖⱼⁱ σXᵢⱼⁱ |Xₖⱼ|<|σXᵢⱼ|) ⟩
  Hᶜ + hⁱ (X k j)                   ≤⟨ +-monoʳ-≤ Hᶜ (m≤m⊔n _ _) ⟩
  Hᶜ + (hⁱ (X k j) ⊔ hⁱ (σ X k j))  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl Xₖⱼ≉σXₖⱼ (inj₁ Xₖⱼⁱ) ⟩
  r (X k j) (σ X k j)              ≤⟨ r≤v k j ⟩
  v                                 ∎

rⁱ-strContrOrbits-σ²X : ∀ {X i j} → 𝑰 (σ (σ X) i j) →
                         ∀ {v} → (∀ k l → r (X k l) (σ X k l) ≤ v) →
                         Hᶜ + hⁱ (σ (σ X) i j) < v
rⁱ-strContrOrbits-σ²X {X} {i} {j} σ²Xᵢⱼⁱ {v} r≤v with σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ (σ X) i j σ²Xᵢⱼⁱ
... | (k , _ , σXₖⱼⁱ , |σXₖⱼ|<|σ²Xᵢⱼ|) with σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ X k j σXₖⱼⁱ
...   | (l , Xₗⱼ≉σXₗⱼ , Xₗⱼⁱ , |Xₗⱼ|<|σXₖⱼ|) = begin
  Hᶜ + hⁱ (σ (σ X) i j)             <⟨ +-monoʳ-< Hᶜ (hⁱ-mono Xₗⱼⁱ σ²Xᵢⱼⁱ (<-trans |Xₗⱼ|<|σXₖⱼ| |σXₖⱼ|<|σ²Xᵢⱼ|)) ⟩
  Hᶜ + hⁱ (X l j)                   ≤⟨ +-monoʳ-≤ Hᶜ (m≤m⊔n _ _) ⟩
  Hᶜ + (hⁱ (X l j) ⊔ hⁱ (σ X l j))  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl Xₗⱼ≉σXₗⱼ (inj₁ Xₗⱼⁱ) ⟩
  r (X l j) (σ X l j)              ≤⟨ r≤v l j ⟩
  v                                 ∎

rⁱ-strContrOn𝑪 : ∀ {X Y i j} → 𝑪ₘ X → 𝑰 (σ Y i j) →
                  ∀ {v} → (∀ k l → r (X k l) (Y k l) ≤ v) →
                  Hᶜ + rⁱ (σ X i j) (σ Y i j) < v
rⁱ-strContrOn𝑪 {X} {Y} {i} {j} Xᶜ σYᵢⱼⁱ {v} r≤v with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ Y i j σYᵢⱼⁱ
... | (k , σYᵢⱼ≈AᵢₖYₖⱼ , Yₖⱼⁱ) = begin
  Hᶜ + rⁱ (σ X i j) (σ Y i j) ≡⟨ cong (Hᶜ +_) (rⁱxᶜyⁱ≡hⁱyⁱ (σ-pres-𝑪ₘ Xᶜ i j) σYᵢⱼⁱ) ⟩
  Hᶜ + hⁱ (σ Y i j)            ≡⟨ cong (Hᶜ +_) (hⁱ-cong σYᵢⱼ≈AᵢₖYₖⱼ) ⟩
  Hᶜ + hⁱ (A i k ▷ Y k j)      <⟨ +-monoʳ-< Hᶜ (hⁱ-decr (𝑰-cong σYᵢⱼ≈AᵢₖYₖⱼ σYᵢⱼⁱ)) ⟩
  Hᶜ + hⁱ (Y k j)              ≡⟨ cong (Hᶜ +_) (sym (rⁱxᶜyⁱ≡hⁱyⁱ (Xᶜ k j) Yₖⱼⁱ)) ⟩
  Hᶜ + rⁱ (X k j) (Y k j)     ≡⟨ H+rⁱ≡r ≈-refl ≈-refl (𝑪𝑰⇒≉ (Xᶜ k j) Yₖⱼⁱ) (inj₂ Yₖⱼⁱ) ⟩
  r (X k j) (Y k j)           ≤⟨ r≤v k j ⟩
  v                           ∎
  where open ≤-Reasoning

rⁱ-strContrOrbits : ∀ {X i j} → 𝑰 (σ X i j) ⊎ 𝑰 (σ (σ X) i j) →
                     ∀ {v} → (∀ k l → r (X k l) (σ X k l) ≤ v) →
                     Hᶜ + rⁱ (σ X i j) (σ (σ X) i j) < v
rⁱ-strContrOrbits {X} {i} {j} σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ {v} r≤v with ≤-total (hⁱ (σ X i j)) (hⁱ (σ (σ X) i j))
... | inj₁ hⁱσXᵢⱼ≤hⁱσ²Xᵢⱼ = subst (_< v) (sym (cong (Hᶜ +_) (m≤n⇒m⊔n≡n hⁱσXᵢⱼ≤hⁱσ²Xᵢⱼ))) (rⁱ-strContrOrbits-σ²X (hⁱ-force-𝑰 σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ hⁱσXᵢⱼ≤hⁱσ²Xᵢⱼ) r≤v)
... | inj₂ hⁱσ²Xᵢⱼ≤hⁱσXᵢⱼ = subst (_< v) (sym (cong (Hᶜ +_) (m≤n⇒n⊔m≡n hⁱσ²Xᵢⱼ≤hⁱσXᵢⱼ))) (rⁱ-strContrOrbits-σX {X} {i} {j} (hⁱ-force-𝑰 (swap σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ) hⁱσ²Xᵢⱼ≤hⁱσXᵢⱼ) r≤v)

------------------------------------------------------------------------
-- r is contracting in the right way

r-strContrOrbits : ∀ {X} →
                    ∀ {v} → 0 < v → (∀ k l → r (X k l) (σ X k l) ≤ v) →
                    ∀ i j → r (σ X i j) (σ (σ X) i j) < v
r-strContrOrbits {X} 0<v r≤v i j
  with σ X i j ≟ σ (σ X) i j | 𝑪? (σ X i j) | 𝑪? (σ (σ X) i j)
... | yes σXᵢⱼ≈σ²Xᵢⱼ | _         | _          = 0<v
... | no  _          | yes σXᵢⱼᶜ | yes σ²Xᵢⱼᶜ = rᶜ-strContrOrbits σXᵢⱼᶜ σ²Xᵢⱼᶜ 0<v r≤v
... | no  _          | no  σXᵢⱼⁱ | _          = rⁱ-strContrOrbits (inj₁ σXᵢⱼⁱ) r≤v
... | no  _          | yes _     | no  σ²Xᵢⱼⁱ = rⁱ-strContrOrbits (inj₂ σ²Xᵢⱼⁱ) r≤v

r-strContrOn𝑪 : ∀ {X Y} → 𝑪ₘ X →
                 ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                 ∀ i j → r (σ X i j) (σ Y i j) < v
r-strContrOn𝑪 {X} {Y} Xᶜ 0<v r≤v i j
  with σ X i j ≟ σ Y i j | 𝑪? (σ X i j) | 𝑪? (σ Y i j)
... | yes σXᵢⱼ≈σYᵢⱼ | _         | _         = 0<v
... | no  σXᵢⱼ≉σYᵢⱼ | yes σXᵢⱼᶜ  | yes σYᵢⱼᶜ = rᶜ-strContrOn𝑪 Xᶜ σXᵢⱼᶜ σYᵢⱼᶜ 0<v r≤v
... | no  σXᵢⱼ≉σYᵢⱼ | yes _     | no  σYᵢⱼⁱ = rⁱ-strContrOn𝑪 Xᶜ σYᵢⱼⁱ r≤v
... | no  σXᵢⱼ≉σYᵢⱼ | no  σXᵢⱼⁱ | _         = contradiction (σ-pres-𝑪ₘ Xᶜ i j) σXᵢⱼⁱ

------------------------------------------------------------------------
-- D is contracting in the right way

open Metric ℝ𝕄ₛ using (_StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)

σ-strContrOrbits : σ StrContrOnOrbitsOver D
σ-strContrOrbits σX≉X = D<v 0<DXσX (r-strContrOrbits 0<DXσX (r≤D _ _))
  where 0<DXσX = Y≉X⇒0<DXY σX≉X

σ-strContrOn𝑪 : ∀ {X Y} → 𝑪ₘ X → Y ≉ₘ X → D (σ X) (σ Y) < D X Y
σ-strContrOn𝑪 Xᶜ Y≉X = D<v 0<DXY (r-strContrOn𝑪 Xᶜ 0<DXY (r≤D _ _))
  where 0<DXY = Y≉X⇒0<DXY Y≉X

σ-strContrOnFP : σ StrContrOnFixedPointOver D
σ-strContrOnFP {X} {X*} σX*≈X* X≉X* = begin
  D X*     (σ X) ≡⟨ D-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σ X}) ⟩
  D (σ X*) (σ X) <⟨ σ-strContrOn𝑪 (fixedPointᶜ σX*≈X*) X≉X* ⟩
  D X*     X     ∎
  where open ≤-Reasoning
