open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_; module ≤-Reasoning)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning; n≢0⇒0<n)
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Function.Metric as Metric
import RoutingLib.Relation.Nullary.Decidable as Dec

open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

open import RoutingLib.Routing using (Network)
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties
import RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra as PathAlgebraProperties
import RoutingLib.Routing.Algebra.Construct.Consistent as Consistent
import RoutingLib.Routing.VectorBased.Core as VectorBasedRoutingCore
import RoutingLib.Routing.VectorBased.Asynchronous as PathVector
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Properties as DistanceVectorProperties
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Properties as PathVectorProperties
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.Metrics as Metrics
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.Properties as MetricProperties
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Properties as DistanceVectorMetricProperties
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.StrictlyContracting as DistanceVectorStrictlyContracting

open ≤-Reasoning

module RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.StrictlyContracting
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  (network : Network algebra n)
  (1≤n : 1 ≤ n)
  where

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open PathAlgebraProperties isRoutingAlgebra isPathAlgebra

open PathVector algebra network hiding (F)

module _ {e : Epoch} {p : Subset n} where

  private
    F : RoutingMatrix → RoutingMatrix
    F = F′ e p

    A : AdjacencyMatrix
    A = Aₜ e p


  open Metrics isRoutingAlgebra isPathAlgebra A public
  open MetricProperties isRoutingAlgebra isPathAlgebra A 1≤n p public

  open Consistent isRoutingAlgebra isPathAlgebra A
  open VectorBasedRoutingCore algebraᶜ Aᶜ using () renaming (F to Fᶜ)
  open PathVectorProperties isRoutingAlgebra isPathAlgebra A

  private
    module DVP  = DistanceVectorMetricProperties isRoutingAlgebraᶜ isFiniteᶜ
    module DVSC = DistanceVectorStrictlyContracting isRoutingAlgebraᶜ isFiniteᶜ (isStrictlyIncreasingᶜ isStrictlyIncreasing)

  ------------------------------------------------------------------------
  -- rⁱ is contracting in the right way

  rⁱ-strContrOrbits-FX : ∀ {X i j} → 𝑰 (F X i j) →
                          ∀ {v} → (∀ k l → r (X k l) (F X k l) ≤ v) →
                          Hᶜ + hⁱ (F X i j) < v
  rⁱ-strContrOrbits-FX {X} {i} {j} FXᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X i j FXᵢⱼⁱ
  ... | (k , Xₖⱼ≉FXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|FXᵢⱼ|) = begin
    Hᶜ + hⁱ (F X i j)                 <⟨ +-monoʳ-< Hᶜ (hⁱ-mono Xₖⱼⁱ FXᵢⱼⁱ |Xₖⱼ|<|FXᵢⱼ|) ⟩
    Hᶜ + hⁱ (X k j)                   ≤⟨ +-monoʳ-≤ Hᶜ (m≤m⊔n _ _) ⟩
    Hᶜ + (hⁱ (X k j) ⊔ hⁱ (F X k j))  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl Xₖⱼ≉FXₖⱼ (inj₁ Xₖⱼⁱ) ⟩
    r (X k j) (F X k j)               ≤⟨ r≤v k j ⟩
    v                                 ∎

  rⁱ-strContrOrbits-F²X : ∀ {X i j} → 𝑰 (F (F X) i j) →
                           ∀ {v} → (∀ k l → r (X k l) (F X k l) ≤ v) →
                           Hᶜ + hⁱ (F (F X) i j) < v
  rⁱ-strContrOrbits-F²X {X} {i} {j} F²Xᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ (F X) i j F²Xᵢⱼⁱ
  ... | (l , _ , FXₗⱼⁱ , |FXₗⱼ|<|F²Xₗⱼ|) with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X l j FXₗⱼⁱ
  ...   | (k , Xₖⱼ≉FXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|FXₖⱼ|) = begin
    Hᶜ + hⁱ (F (F X) i j)             <⟨ +-monoʳ-< Hᶜ (hⁱ-mono Xₖⱼⁱ F²Xᵢⱼⁱ (<-trans |Xₖⱼ|<|FXₖⱼ| |FXₗⱼ|<|F²Xₗⱼ|)) ⟩
    Hᶜ + hⁱ (X k j)                   ≤⟨ +-monoʳ-≤ Hᶜ (m≤m⊔n _ _) ⟩
    Hᶜ + (hⁱ (X k j) ⊔ hⁱ (F X k j))  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl Xₖⱼ≉FXₖⱼ (inj₁ Xₖⱼⁱ) ⟩
    r (X k j) (F X k j)               ≤⟨ r≤v k j ⟩
    v                                 ∎

  rⁱ-strContrOn𝑪 : ∀ {X Y i j} → 𝑪ₘ X → 𝑰 (F Y i j) →
                    ∀ {v} → (∀ k l → r (X k l) (Y k l) ≤ v) →
                    Hᶜ + rⁱ (F X i j) (F Y i j) < v
  rⁱ-strContrOn𝑪 {X} {Y} {i} {j} Xᶜ FYᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ Y i j FYᵢⱼⁱ
  ... | (k , FYᵢⱼ≈AᵢₖYₖⱼ , Yₖⱼⁱ) = begin
    Hᶜ + rⁱ (F X i j) (F Y i j)  ≡⟨ cong (Hᶜ +_) (rⁱxᶜyⁱ≡hⁱyⁱ (F-pres-𝑪ₘ Xᶜ i j) FYᵢⱼⁱ) ⟩
    Hᶜ + hⁱ (F Y i j)            ≡⟨ cong (Hᶜ +_) (hⁱ-cong FYᵢⱼ≈AᵢₖYₖⱼ) ⟩
    Hᶜ + hⁱ (A i k ▷ Y k j)      <⟨ +-monoʳ-< Hᶜ (hⁱ-decr (𝑰-cong FYᵢⱼ≈AᵢₖYₖⱼ FYᵢⱼⁱ)) ⟩
    Hᶜ + hⁱ (Y k j)              ≡⟨ cong (Hᶜ +_) (sym (rⁱxᶜyⁱ≡hⁱyⁱ (Xᶜ k j) Yₖⱼⁱ)) ⟩
    Hᶜ + rⁱ (X k j) (Y k j)      ≡⟨ H+rⁱ≡r ≈-refl ≈-refl (𝑪𝑰⇒≉ (Xᶜ k j) Yₖⱼⁱ) (inj₂ Yₖⱼⁱ) ⟩
    r (X k j) (Y k j)            ≤⟨ r≤v k j ⟩
    v                            ∎
    where open ≤-Reasoning

  rⁱ-strContrOrbits : ∀ {X i j} → 𝑰 (F X i j) ⊎ 𝑰 (F (F X) i j) →
                       ∀ {v} → (∀ k l → r (X k l) (F X k l) ≤ v) →
                       Hᶜ + rⁱ (F X i j) (F (F X) i j) < v
  rⁱ-strContrOrbits {X} {i} {j} FXᵢⱼⁱ⊎F²Xᵢⱼⁱ {v} r≤v with ≤-total (hⁱ (F X i j)) (hⁱ (F (F X) i j))
  ... | inj₁ hⁱFXᵢⱼ≤hⁱF²Xᵢⱼ = subst (_< v) (sym (cong (Hᶜ +_) (m≤n⇒m⊔n≡n hⁱFXᵢⱼ≤hⁱF²Xᵢⱼ))) (rⁱ-strContrOrbits-F²X (hⁱ-force-𝑰 FXᵢⱼⁱ⊎F²Xᵢⱼⁱ hⁱFXᵢⱼ≤hⁱF²Xᵢⱼ) r≤v)
  ... | inj₂ hⁱF²Xᵢⱼ≤hⁱFXᵢⱼ = subst (_< v) (sym (cong (Hᶜ +_) (m≤n⇒n⊔m≡n hⁱF²Xᵢⱼ≤hⁱFXᵢⱼ))) (rⁱ-strContrOrbits-FX {X} {i} {j} (hⁱ-force-𝑰 (swap FXᵢⱼⁱ⊎F²Xᵢⱼⁱ) hⁱF²Xᵢⱼ≤hⁱFXᵢⱼ) r≤v)


  ------------------------------------------------------------------------
  -- rᶜ is contracting in the right way

  rᶜ-strContr-𝑪𝑪 : ∀ {X Y} → (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) →
                   ∀ {i j} (FXᵢⱼᶜ : 𝑪 (F X i j)) (FYᵢⱼᶜ : 𝑪 (F Y i j)) →
                   ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                   rᶜ FXᵢⱼᶜ FYᵢⱼᶜ < v
  rᶜ-strContr-𝑪𝑪 {X} {Y} Xᶜ Yᶜ {i} {j} FXᵢⱼᶜ FYᵢⱼᶜ {v} 0<v r≤v = begin
    rᶜ FXᵢⱼᶜ FYᵢⱼᶜ                           ≡⟨⟩
    DV.r (toCRoute FXᵢⱼᶜ) (toCRoute FYᵢⱼᶜ)   ≡⟨ DVP.r-cong ≈-refl ≈-refl ⟩
    DV.r (cFX i j) (cFY i j)                 ≡⟨ DVP.r-cong (F-toCMatrix-commute Xᶜ (F-pres-𝑪ₘ Xᶜ) i j) (F-toCMatrix-commute Yᶜ (F-pres-𝑪ₘ Yᶜ) i j) ⟩
    DV.r (Fᶜ cX i j) (Fᶜ cY i j)             <⟨ DVSC.r[FXᵢⱼ,FYᵢⱼ]<v Aᶜ cX cY i j 0<v d≤v ⟩
    v                                        ∎
    where
    cX  = toCMatrix Xᶜ
    cFX = toCMatrix (F-pres-𝑪ₘ Xᶜ)
    cY  = toCMatrix Yᶜ
    cFY = toCMatrix (F-pres-𝑪ₘ Yᶜ)
    d≤v : ∀ k → cX k j ≉ᶜ cY k j → DV.r (cX k j) (cY k j) ≤ v
    d≤v k cXₖⱼ≉cYₖⱼ = begin
      DV.r (cX k j) (cY k j) ≡⟨⟩
      rᶜ  (Xᶜ k j) (Yᶜ k j) ≡⟨ rᶜ≡r (Xᶜ k j) (Yᶜ k j) ≈-refl ≈-refl cXₖⱼ≉cYₖⱼ ⟩
      r   (X k j)  (Y k j)  ≤⟨ r≤v k j ⟩
      v                      ∎
      where open ≤-Reasoning

  rᶜ-strContr-𝑪𝑰 : ∀ {X Y i j} → (𝑰ₘ X × 𝑪ₘ Y) ⊎ (𝑪ₘ X × 𝑰ₘ Y) →
                   (FXᵢⱼᶜ : 𝑪 (F X i j)) (FYᵢⱼᶜ : 𝑪 (F Y i j)) →
                   ∀ {v} → (∀ k l → r (X k l) (Y k l) ≤ v) →
                   rᶜ FXᵢⱼᶜ FYᵢⱼᶜ < v
  rᶜ-strContr-𝑪𝑰 {X} {Y} (inj₁ (Xⁱ , Yᶜ)) FXᵢⱼᶜ FYᵢⱼᶜ {v} r≤v with 𝑰ₘ-witness Xⁱ
  ...   | (k , l , Xₖₗⁱ) = begin
    rᶜ FXᵢⱼᶜ  FYᵢⱼᶜ            <⟨ rᶜ<Hᶜ+x FXᵢⱼᶜ FYᵢⱼᶜ _ ⟩
    Hᶜ + rⁱ (X k l) (Y k l)  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl (𝑪𝑰⇒≉ (Yᶜ k l) Xₖₗⁱ ∘ ≈-sym) (inj₁ Xₖₗⁱ) ⟩
    r (X k l) (Y k l)        ≤⟨ r≤v k l ⟩
    v                        ∎
    where open ≤-Reasoning
  rᶜ-strContr-𝑪𝑰 {X} {Y} (inj₂ (Xᶜ , Yⁱ)) FXᵢⱼᶜ FYᵢⱼᶜ {v} r≤v with 𝑰ₘ-witness Yⁱ
  ... | (k , l , Yₖₗⁱ) = begin
    rᶜ FXᵢⱼᶜ  FYᵢⱼᶜ            <⟨ rᶜ<Hᶜ+x FXᵢⱼᶜ FYᵢⱼᶜ _ ⟩
    Hᶜ + rⁱ (X k l) (Y k l)  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl (𝑪𝑰⇒≉ (Xᶜ k l) Yₖₗⁱ) (inj₂ Yₖₗⁱ) ⟩
    r (X k l) (Y k l)        ≤⟨ r≤v k l ⟩
    v                        ∎
    where open ≤-Reasoning

  rᶜ-strContrOrbits : ∀ {X i j} →
                       (FXᵢⱼᶜ : 𝑪 (F X i j)) (F²Xᵢⱼᶜ : 𝑪 (F (F X) i j)) →
                       ∀ {v} → 0 < v → (∀ k l → r (X k l) (F X k l) ≤ v) →
                       rᶜ FXᵢⱼᶜ F²Xᵢⱼᶜ < v
  rᶜ-strContrOrbits {X} {i} {j} FXᵢⱼᶜ F²Xᵢⱼᶜ {v} 0<v r≤v with 𝑪ₘ? X | 𝑪ₘ? (F X)
  ... | yes Xᶜ | yes FXᶜ = rᶜ-strContr-𝑪𝑪 Xᶜ FXᶜ FXᵢⱼᶜ F²Xᵢⱼᶜ 0<v r≤v
  ... | yes Xᶜ | no  FXⁱ = contradiction (F-pres-𝑪ₘ Xᶜ) FXⁱ
  ... | no  Xⁱ | yes FXᶜ = rᶜ-strContr-𝑪𝑰 (inj₁ (Xⁱ , FXᶜ)) FXᵢⱼᶜ F²Xᵢⱼᶜ r≤v
  ... | no  Xⁱ | no  FXⁱ with 𝑰ₘ-witness FXⁱ
  ...   | (m , n , FXₘₙⁱ) with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X m n FXₘₙⁱ
  ...     | (k , Xₖₙ≉FXₖₙ , Xₖₙⁱ , _) = begin
    rᶜ FXᵢⱼᶜ  F²Xᵢⱼᶜ            <⟨ rᶜ<Hᶜ+x FXᵢⱼᶜ F²Xᵢⱼᶜ _ ⟩
    Hᶜ + rⁱ (X k n) (F X k n) ≡⟨ H+rⁱ≡r ≈-refl ≈-refl Xₖₙ≉FXₖₙ (inj₁ Xₖₙⁱ) ⟩
    r (X k n) (F X k n)       ≤⟨ r≤v k n ⟩
    v                         ∎
    where open ≤-Reasoning

  rᶜ-strContrOn𝑪 : ∀ {X Y} → 𝑪ₘ X →
                    ∀ {i j} → (FXᵢⱼᶜ : 𝑪 (F X i j)) (FYᵢⱼᶜ : 𝑪 (F Y i j)) →
                    ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                    rᶜ FXᵢⱼᶜ FYᵢⱼᶜ < v
  rᶜ-strContrOn𝑪 {X} {Y} Xᶜ {i} {j} FXᵢⱼᶜ FYᵢⱼᶜ 0<v r≤v with 𝑪ₘ? Y
  ... | yes Yᶜ = rᶜ-strContr-𝑪𝑪 Xᶜ Yᶜ FXᵢⱼᶜ FYᵢⱼᶜ 0<v r≤v
  ... | no  Yⁱ = rᶜ-strContr-𝑪𝑰 (inj₂ (Xᶜ , Yⁱ)) FXᵢⱼᶜ FYᵢⱼᶜ r≤v


  ------------------------------------------------------------------------
  -- r is contracting in the right way

  r-strContrOrbits : ∀ {X} →
                     ∀ {v} → 0 < v → (∀ k l → r (X k l) (F X k l) ≤ v) →
                     ∀ i j → r (F X i j) (F (F X) i j) < v
  r-strContrOrbits {X} 0<v r≤v i j
    with F X i j ≟ F (F X) i j | 𝑪? (F X i j) | 𝑪? (F (F X) i j)
  ... | yes FXᵢⱼ≈F²Xᵢⱼ | _         | _          = 0<v
  ... | no  _          | yes FXᵢⱼᶜ | yes F²Xᵢⱼᶜ  = rᶜ-strContrOrbits FXᵢⱼᶜ F²Xᵢⱼᶜ 0<v r≤v
  ... | no  _          | no  FXᵢⱼⁱ | _          = rⁱ-strContrOrbits (inj₁ FXᵢⱼⁱ) r≤v
  ... | no  _          | yes _     | no  F²Xᵢⱼⁱ = rⁱ-strContrOrbits (inj₂ F²Xᵢⱼⁱ) r≤v

  r-strContrOn𝑪 : ∀ {X Y} → 𝑪ₘ X →
                   ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                   ∀ i j → r (F X i j) (F Y i j) < v
  r-strContrOn𝑪 {X} {Y} Xᶜ 0<v r≤v i j
    with F X i j ≟ F Y i j | 𝑪? (F X i j) | 𝑪? (F Y i j)
  ... | yes FXᵢⱼ≈FYᵢⱼ | _         | _         = 0<v
  ... | no  FXᵢⱼ≉FYᵢⱼ | yes FXᵢⱼᶜ  | yes FYᵢⱼᶜ = rᶜ-strContrOn𝑪 Xᶜ FXᵢⱼᶜ FYᵢⱼᶜ 0<v r≤v
  ... | no  FXᵢⱼ≉FYᵢⱼ | yes _     | no  FYᵢⱼⁱ = rⁱ-strContrOn𝑪 Xᶜ FYᵢⱼⁱ r≤v
  ... | no  FXᵢⱼ≉FYᵢⱼ | no  FXᵢⱼⁱ | _         = contradiction (F-pres-𝑪ₘ Xᶜ i j) FXᵢⱼⁱ

------------------------------------------------------------------------
-- d is contracting in the right ways

-- These two lemmas are a mess as can't pattern match on `i ∈? p` directly
-- as it unfolds the adjacency matrix

  d[FXᵢ,F²Xᵢ]<D[X,FX] : ∀ {X} → WellFormed p X → F X ≉ₘ[ p ] X →
                  ∀ i → dᶜ p i (F X i) (F (F X) i) < D p X (F X)
  d[FXᵢ,F²Xᵢ]<D[X,FX] {X} wfX FX≉X i with Y≉ₚX⇒0<DXY p FX≉X
  ... | 0<DXY with max[t]<x 0<DXY (r-strContrOrbits 0<DXY (r≤D-wf p wfX (F′-inactive network e p X)) i)
  ...   | d[FXᵢ,F²Xᵢ]<D[X,FX] = Dec.[
        (λ i∈p → subst (_< D p X (F X)) (sym (Condition.accept d (_∈? p) i∈p)) d[FXᵢ,F²Xᵢ]<D[X,FX]) ,
        (λ i∉p → subst (_< D p X (F X)) (sym (Condition.reject d (_∈? p) i∉p)) 0<DXY)
      ] (i ∈? p)

  dₜFXᵢFYᵢ<DXY : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X →
                 𝑪ₘ X → ∀ i → dᶜ p i (F X i) (F Y i) < D p X Y
  dₜFXᵢFYᵢ<DXY {X} {Y} wfX wfY Y≉X Xᶜ i with Y≉ₚX⇒0<DXY p Y≉X
  ... | 0<DXY with max[t]<x 0<DXY (r-strContrOn𝑪 Xᶜ 0<DXY (r≤D-wf p wfX wfY) i)
  ...   | d[FXᵢ,F²Xᵢ]<D[X,FX] = Dec.[
        (λ i∈p → subst (_< D p X Y) (sym (Condition.accept d (_∈? p) i∈p)) d[FXᵢ,F²Xᵢ]<D[X,FX]) ,
        (λ i∉p → subst (_< D p X Y) (sym (Condition.reject d (_∈? p) i∉p)) 0<DXY)
      ] (i ∈? p)

------------------------------------------------------------------------
-- D is contracting in the right ways

  Fₜ-strContrOnOrbits : ∀ {X} → WellFormed p X → (F X) ≉ₘ[ p ] X →
                       D p (F X) (F (F X)) < D p X (F X)
  Fₜ-strContrOnOrbits {X} wfX FX≉X = max[t]<x (Y≉ₚX⇒0<DXY p FX≉X) (d[FXᵢ,F²Xᵢ]<D[X,FX] wfX FX≉X)

  Fₜ-strContrOn𝑪 : ∀ {X Y} → WellFormed p X → WellFormed p Y → Y ≉ₘ[ p ] X → 𝑪ₘ X →
                   D p (F X) (F Y) < D p X Y
  Fₜ-strContrOn𝑪 wfX wfY Y≉X Xᶜ = max[t]<x (Y≉ₚX⇒0<DXY p Y≉X) (dₜFXᵢFYᵢ<DXY wfX wfY Y≉X Xᶜ)

  Fₜ-strContrOnFP : ∀ {X} → WellFormed p X → ∀ {X*} → F X* ≈ₘ X* → X ≉ₘ[ p ] X* →
                   D p X* (F X) < D p X* X
  Fₜ-strContrOnFP {X} wfX {X*} FX*≈X* X≉X* = begin
    D p X*     (F X) ≡⟨ D-cong p (≈ₘ-sym FX*≈X*) (≈ₘ-refl {x = F′ e p X}) ⟩
    D p (F X*) (F X) <⟨ Fₜ-strContrOn𝑪 (X*-wf network e p FX*≈X*) wfX X≉X* (fixedPointᶜ FX*≈X*) ⟩
    D p X*     X     ∎
    where open ≤-Reasoning

open DistanceVectorProperties isRoutingAlgebra network

F∥-isAMCO : AMCO F∥
F∥-isAMCO = record
  { dᵢ                   = λ e p → d {e} {p}
  ; dᵢ-isQuasiSemiMetric = λ e p i → d-isQuasiSemiMetric
  ; dᵢ-bounded           = λ e p → proj₁ d-bounded , proj₂ d-bounded
  ; F-strContrOnOrbits  = Fₜ-strContrOnOrbits
  ; F-strContrOnFP      = Fₜ-strContrOnFP
  ; F-inactive          = F′-inactive
  }
