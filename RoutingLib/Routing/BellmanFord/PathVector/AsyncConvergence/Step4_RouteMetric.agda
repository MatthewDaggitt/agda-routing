open import Data.Product using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≮_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; n≤1+n; m+n∸m≡n; n≤m+n; +-mono-≤;
        ∸-mono;  ⊓-mono-<;+-cancelˡ-≤;  m≤m⊔n; m⊓n≤m; ≰⇒≥; <⇒≱; <⇒≯; n≤m⊔n;
        m⊓n≤n; <-transˡ; <-transʳ; +-distribˡ-⊔; <⇒≤; +-comm; ≤-stepsʳ; +-monoʳ-≤; +-monoʳ-<)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; ⊤; ⁅_⁆)
open import Data.Fin.Subset.Properties using (x∈p∩q⁺; x∈⁅x⁆; ∈⊤)
open import Data.Fin.Dec using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; cong₂)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using () renaming (SufficientConditions to GeneralSufficientConditions)
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m; m<n⇒n≢0; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Fin.Subset using (_\\_) renaming (size to sizeₛ)
open import RoutingLib.Data.Fin.Subset.Properties using (size[p\\q]<size[p]; i∉p\\q⇒i∉p; i∉⁅j⁆)
import RoutingLib.Function.Metric as Metric
import RoutingLib.Function.Metric.MaxLift as MaxLift

import RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Step2_InconsistentRouteMetric as Step2
import RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Step3_ConsistentRouteMetric as Step3

module RoutingLib.Routing.BellmanFord.PathVector.AsyncConvergence.Step4_RouteMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step2 𝓟𝓢𝓒
  open Step3 𝓟𝓢𝓒
  open Metric S using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)

  abstract
  
    Hᶜ : ℕ
    Hᶜ = suc (proj₁ dᵣᶜ-bounded)

    Hⁱ : ℕ
    Hⁱ = proj₁ dᵣⁱ-bounded

    dᵣᶜ<Hᶜ : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ < Hᶜ
    dᵣᶜ<Hᶜ xᶜ yᶜ = s≤s (proj₂ dᵣᶜ-bounded xᶜ yᶜ)
    
    dᵣᶜ<Hᶜ+x : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) z → dᵣᶜ xᶜ yᶜ < Hᶜ + z
    dᵣᶜ<Hᶜ+x xᶜ yᶜ z = s≤s (≤-trans (proj₂ dᵣᶜ-bounded xᶜ yᶜ) (m≤m+n _ z))

    Hᶜ<Hᶜ+dᵣⁱ : ∀ x y → Hᶜ < Hᶜ + dᵣⁱ x y
    Hᶜ<Hᶜ+dᵣⁱ x y = begin
      1 + Hᶜ       ≡⟨ +-comm 1 Hᶜ ⟩
      Hᶜ + 1       ≤⟨ +-monoʳ-≤ Hᶜ (1≤dᵣⁱ x y) ⟩
      Hᶜ + dᵣⁱ x y ∎
      where open ≤-Reasoning

    --------------------------------
    -- An ultrametric over tables --
    --------------------------------

    dᵣ : Route → Route → ℕ
    dᵣ x y with x ≟ y | 𝑪? x | 𝑪? y
    ... | yes _ | _      | _      = zero
    ... | no  _ | yes xᶜ | yes yᶜ = dᵣᶜ xᶜ yᶜ
    ... | no  _ | _      | _      = Hᶜ + dᵣⁱ x y
  
    dᵣ-cong : dᵣ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dᵣ-cong {W} {X} {Y} {Z} W≈X Y≈Z with W ≟ Y | X ≟ Z 
    ... | yes _   | yes _   = refl
    ... | yes W≈Y | no  X≉Z = contradiction (≈-trans (≈-trans (≈-sym W≈X) W≈Y) Y≈Z) X≉Z
    ... | no  W≉Y | yes X≈Z = contradiction (≈-trans (≈-trans W≈X X≈Z) (≈-sym Y≈Z)) W≉Y
    ... | no _    | no _    with 𝑪? W | 𝑪? X | 𝑪? Y | 𝑪? Z
    ...   | no  Wⁱ | yes Xᶜ | _      | _      = contradiction (𝑪-cong (≈-sym W≈X) Xᶜ) Wⁱ
    ...   | yes Wᶜ | no  Xⁱ | _      |  _     = contradiction (𝑪-cong W≈X Wᶜ) Xⁱ
    ...   | _      | _      | yes Yᶜ | no  Zⁱ = contradiction (𝑪-cong Y≈Z Yᶜ) Zⁱ
    ...   | _      | _      | no  Yⁱ | yes Zᶜ = contradiction (𝑪-cong (≈-sym Y≈Z) Zᶜ) Yⁱ
    ...   | no _   | no _   | _      | _      = cong (Hᶜ +_) (dᵣⁱ-cong W≈X Y≈Z)
    ...   | yes _  | yes _  | no  _  | no  _  = cong (Hᶜ +_) (dᵣⁱ-cong W≈X Y≈Z)
    ...   | yes wᶜ | yes xᶜ | yes yᶜ | yes zᶜ = dᵣᶜ-cong wᶜ yᶜ xᶜ zᶜ W≈X Y≈Z
  
    x≈y⇒dᵣ≡0 : ∀ {X Y} → X ≈ Y → dᵣ X Y ≡ 0
    x≈y⇒dᵣ≡0 {X} {Y} X≈Y with X ≟ Y
    ... | yes _   = refl
    ... | no  X≉Y = contradiction X≈Y X≉Y

    dᵣ≡0⇒x≈y : ∀ {X Y} → dᵣ X Y ≡ 0 → X ≈ Y
    dᵣ≡0⇒x≈y {X} {Y} dᵣ≡0 with X ≟ Y
    ... | yes X≈Y = X≈Y
    ... | no  _   with 𝑪? X | 𝑪? Y
    ...   | yes Xᶜ | yes Yᶜ  = dᵣᶜ≡0⇒x≈y Xᶜ Yᶜ dᵣ≡0
    ...   | no  Xⁱ | _      = contradiction dᵣ≡0 λ()
    ...   | yes Xᶜ | no  Yⁱ = contradiction dᵣ≡0 λ()
  
    dᵣ-sym : ∀ X Y → dᵣ X Y ≡ dᵣ Y X
    dᵣ-sym X Y with X ≟ Y | Y ≟ X
    ... | yes _   | yes _   = refl
    ... | yes X≈Y | no  Y≉X = contradiction (≈-sym X≈Y) Y≉X
    ... | no  X≉Y | yes Y≈X = contradiction (≈-sym Y≈X) X≉Y
    ... | no _    | no _    with 𝑪? X | 𝑪? Y
    ...   | yes Xᶜ | yes Yᶜ = dᵣᶜ-sym Xᶜ Yᶜ
    ...   | no  _  | no  _  = cong (Hᶜ +_) (dᵣⁱ-sym X Y)
    ...   | no  _  | yes _  = cong (Hᶜ +_) (dᵣⁱ-sym X Y)
    ...   | yes _  | no  _  = cong (Hᶜ +_) (dᵣⁱ-sym X Y)

    dᵣ-maxTriIneq-lemma : ∀ X Y Z → Hᶜ + dᵣⁱ X Z ≤ (Hᶜ + dᵣⁱ X Y) ⊔ (Hᶜ + dᵣⁱ Y Z)
    dᵣ-maxTriIneq-lemma X Y Z = begin
      Hᶜ + dᵣⁱ X Z                    ≤⟨ +-monoʳ-≤ Hᶜ (dᵣⁱ-maxTriIneq X Y Z) ⟩
      Hᶜ + (dᵣⁱ X Y ⊔ dᵣⁱ Y Z)        ≡⟨ +-distribˡ-⊔ Hᶜ _ _ ⟩
      (Hᶜ + dᵣⁱ X Y) ⊔ (Hᶜ + dᵣⁱ Y Z) ∎
      where open ≤-Reasoning
  
    dᵣ-maxTriIneq : MaxTriangleIneq dᵣ
    dᵣ-maxTriIneq x y z with x ≟ z | x ≟ y | y ≟ z
    dᵣ-maxTriIneq x y z | yes _   | _       | _       = z≤n
    dᵣ-maxTriIneq x y z | no  x≉z | yes x≈y | yes y≈z = contradiction (≈-trans x≈y y≈z) x≉z
    dᵣ-maxTriIneq x y z | no  _   | yes x≈y | no  _   with 𝑪? x | 𝑪? y | 𝑪? z
    ... | yes xᶜ | yes yᶜ | yes zᶜ = ≤-reflexive (dᵣᶜ-cong xᶜ zᶜ yᶜ zᶜ x≈y ≈-refl)
    ... | yes xᶜ | no  yⁱ | _     = contradiction (𝑪-cong x≈y xᶜ) yⁱ
    ... | no  xⁱ | yes yᶜ | _     = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
    ... | yes _  | yes _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (dᵣⁱ-cong x≈y ≈-refl))
    ... | no  _  | no  _  | yes _ = +-monoʳ-≤ Hᶜ (≤-reflexive (dᵣⁱ-cong x≈y ≈-refl))
    ... | no  _  | no  _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (dᵣⁱ-cong x≈y ≈-refl))
    dᵣ-maxTriIneq x y z | no  _   | no  _   | yes y≈z with 𝑪? x | 𝑪? y | 𝑪? z
    ... | yes xᶜ | yes yᶜ | yes zᶜ = m≤n⇒m≤n⊔o 0 (≤-reflexive (dᵣᶜ-cong xᶜ zᶜ xᶜ yᶜ ≈-refl (≈-sym y≈z)))
    ... | _      | yes yᶜ | no  zⁱ = contradiction (𝑪-cong y≈z yᶜ) zⁱ
    ... | _      | no  yⁱ | yes zᶜ = contradiction (𝑪-cong (≈-sym y≈z) zᶜ) yⁱ
    ... | no  _  | yes _  | yes _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (dᵣⁱ-cong ≈-refl (≈-sym y≈z))))
    ... | yes _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (dᵣⁱ-cong ≈-refl (≈-sym y≈z))))
    ... | no  _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (dᵣⁱ-cong ≈-refl (≈-sym y≈z))))
    dᵣ-maxTriIneq x y z | no  _   | no  _   | no  _   with 𝑪? x | 𝑪? y | 𝑪? z
    ... | yes xᶜ | yes yᶜ | yes zᶜ = dᵣᶜ-maxTriIneq xᶜ yᶜ zᶜ
    ... | yes xᶜ | yes yᶜ | no  zⁱ = m≤o⇒m≤n⊔o (dᵣᶜ xᶜ yᶜ) (+-monoʳ-≤ Hᶜ (xᶜyᶜzⁱ⇒dᵣⁱxz≤dᵣⁱyz xᶜ yᶜ zⁱ))
    ... | no  xⁱ | yes yᶜ | yes zᶜ = m≤n⇒m≤n⊔o (dᵣᶜ yᶜ zᶜ) (+-monoʳ-≤ Hᶜ (xⁱyᶜzᶜ⇒dᵣⁱxz≤dᵣⁱxy xⁱ yᶜ zᶜ))
    ... | yes xᶜ | no  yⁱ | yes zᶜ = m≤n⇒m≤n⊔o (Hᶜ + dᵣⁱ y z) (<⇒≤ (dᵣᶜ<Hᶜ+x xᶜ zᶜ _))
    ... | yes _  | no  _  | no  _  = dᵣ-maxTriIneq-lemma x y z
    ... | no  _  | yes _  | no  _  = dᵣ-maxTriIneq-lemma x y z
    ... | no  _  | no  _  | yes _  = dᵣ-maxTriIneq-lemma x y z
    ... | no  _  | no  _  | no  _  = dᵣ-maxTriIneq-lemma x y z


    dᵣ≤Hᶜ+Hⁱ : ∀ x y → dᵣ x y ≤ Hᶜ + Hⁱ
    dᵣ≤Hᶜ+Hⁱ x y with x ≟ y
    ... | yes _ = z≤n
    ... | no  _ with 𝑪? x | 𝑪? y
    ...   | yes xᶜ | yes yᶜ = ≤-trans (proj₂ dᵣᶜ-bounded xᶜ yᶜ) (≤-trans (n≤1+n _) (m≤m+n Hᶜ Hⁱ))
    ...   | no  _  | no  _  = +-monoʳ-≤ Hᶜ (proj₂ dᵣⁱ-bounded x y)
    ...   | no  _  | yes _  = +-monoʳ-≤ Hᶜ (proj₂ dᵣⁱ-bounded x y)
    ...   | yes _  | no  _  = +-monoʳ-≤ Hᶜ (proj₂ dᵣⁱ-bounded x y)
  
    dᵣ-bounded : Bounded dᵣ
    dᵣ-bounded = Hᶜ + Hⁱ , dᵣ≤Hᶜ+Hⁱ
  
    dᵣ-isUltrametric : IsUltrametric dᵣ
    dᵣ-isUltrametric = record
      { cong        = dᵣ-cong
      ; eq⇒0        = x≈y⇒dᵣ≡0
      ; 0⇒eq        = dᵣ≡0⇒x≈y
      ; sym         = dᵣ-sym
      ; maxTriangle = dᵣ-maxTriIneq
      }

  dᵣ-ultrametric : Ultrametric
  dᵣ-ultrametric = record
    { d             = dᵣ
    ; isUltrametric = dᵣ-isUltrametric
    }


  abstract
  
    private

      H<dᵣ : ∀ {x y} → x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ < dᵣ x y 
      H<dᵣ {x} {y} x≉y xⁱ⊎yⁱ with x ≟ y
      ... | yes x≈y = contradiction x≈y x≉y
      ... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
      ... | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
      ... | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ 
      ... | no  _  | _      | _       = Hᶜ<Hᶜ+dᵣⁱ x y
      ... | yes _  | no  _  | _       = Hᶜ<Hᶜ+dᵣⁱ x y
      
      dᵣᶜ<dᵣ : ∀ {w x y z} (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) → y ≉ z → 𝑰 y ⊎ 𝑰 z  → dᵣᶜ wᶜ xᶜ < dᵣ y z
      dᵣᶜ<dᵣ wᶜ xᶜ y≉z yⁱ⊎zⁱ = <-transʳ (<⇒≤ (dᵣᶜ<Hᶜ wᶜ xᶜ)) (H<dᵣ y≉z yⁱ⊎zⁱ)

      dᵣᶜ≤dᵣ : ∀ {x y} → x ≉ y → (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ ≤ dᵣ x y
      dᵣᶜ≤dᵣ {x} {y} x≉y xᶜ yᶜ with x ≟ y
      ... | yes x≈y = contradiction x≈y x≉y
      ... | no  _   with 𝑪? x | 𝑪? y
      ...   | yes _  | yes _  = ≤-reflexive (dᵣᶜ-cong _ _ _ _ ≈-refl ≈-refl)
      ...   | no  xⁱ | _      = contradiction xᶜ xⁱ
      ...   | yes _  | no  yⁱ = contradiction yᶜ yⁱ
      
      H+dᵣⁱ≤dᵣ : ∀ {x y} → x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ + dᵣⁱ x y ≤ dᵣ x y
      H+dᵣⁱ≤dᵣ {x} {y} x≉y xⁱ⊎yⁱ with x ≟ y
      ... | yes x≈y = contradiction x≈y x≉y
      ... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
      ... | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
      ... | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ 
      ... | no  _  | _      | _       = ≤-refl
      ... | yes _  | no  _  | _       = ≤-refl

      dᵣ-force-dᵣⁱ : ∀ (X Y : RMatrix) {r s} → 
                    (∀ u v → dᵣ (X u v) (Y u v) ≤ Hᶜ + dᵣⁱ (X r s) (Y r s)) →
                    (∀ {u v} → X u v ≉ Y u v → 𝑰 (X u v) ⊎ 𝑰 (Y u v) →
                      dᵣⁱ (X u v) (Y u v) ≤ dᵣⁱ (X r s) (Y r s))
      dᵣ-force-dᵣⁱ X Y {r} {s} dᵣ≤Hᶜ+dᵣⁱXₗYₗ {u} {v} Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ =
        +-cancelˡ-≤ Hᶜ (≤-trans (H+dᵣⁱ≤dᵣ Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ) (dᵣ≤Hᶜ+dᵣⁱXₗYₗ u v))


    dᵣ-strContrOrbitsⁱ : ∀ {X i j r s} →
                       (∀ u v → dᵣ (X u v) (σ X u v) ≤ Hᶜ + dᵣⁱ (X r s) (σ X r s)) →
                       dᵣ (σ X i j) (σ (σ X) i j) < Hᶜ + dᵣⁱ (X r s) (σ X r s)
    dᵣ-strContrOrbitsⁱ {X} {i} {j} {r} {s} dᵣ≤Hᶜ+dᵣⁱ with σ X i j ≟ σ (σ X) i j
    ... | yes σXₖ≈σYₖ = s≤s z≤n
    ... | no  σXₖ≉σYₖ with 𝑪? (σ X i j) | 𝑪? (σ (σ X) i j)
    ...   | yes σXᵢⱼᶜ | yes σ²Xᵢⱼᶜ = dᵣᶜ<Hᶜ+x σXᵢⱼᶜ σ²Xᵢⱼᶜ _
    ...   | no  σXᵢⱼⁱ | _          = +-monoʳ-< Hᶜ (dᵣⁱ-strContrOrbits X (dᵣ-force-dᵣⁱ X (σ X) dᵣ≤Hᶜ+dᵣⁱ) (inj₁ σXᵢⱼⁱ))
    ...   | yes _     | no  σ²Xᵢⱼⁱ = +-monoʳ-< Hᶜ (dᵣⁱ-strContrOrbits X (dᵣ-force-dᵣⁱ X (σ X) dᵣ≤Hᶜ+dᵣⁱ) (inj₂ σ²Xᵢⱼⁱ))


    chain₂ : ∀ X i j k → 𝑰 (σ X i j) → σ X i j ≈ A i k ▷ X k j →
             X k j ≈ σ X k j → size (σ X k j) < size (σ X i j)
    chain₂ X i j k σXᵢⱼⁱ σXᵢⱼ≈AᵢₖXₖⱼ Xₖⱼ≈σXₖⱼ
      with ≈-trans σXᵢⱼ≈AᵢₖXₖⱼ (▷-cong (A i k) Xₖⱼ≈σXₖⱼ)
    ... | σXᵢⱼ≈Aᵢₖ▷σXₖⱼ = begin
        size (σ X k j)         <⟨ ≤-reflexive (size-incr (𝑰-cong σXᵢⱼ≈Aᵢₖ▷σXₖⱼ σXᵢⱼⁱ)) ⟩
        size (A i k ▷ σ X k j) ≡⟨ sym (size-cong σXᵢⱼ≈Aᵢₖ▷σXₖⱼ) ⟩
        size (σ X i j)         ∎
        where open ≤-Reasoning


    reduction : ∀ X l j → 𝑰 (σ X l j) → Acc _<_ (size (σ X l j)) →
                ∃ λ k → Hᶜ < dᵣ (X k j) (σ X k j)  
    reduction X l j σXₗⱼⁱ (acc rec) with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X _ _ σXₗⱼⁱ
    ... | (k , σXₗⱼ≈AᵢₖXₖⱼ , Xₖⱼⁱ) with X k j ≟ σ X k j
    ...   | no  Xₖⱼ≉σXₖⱼ = k , H<dᵣ Xₖⱼ≉σXₖⱼ (inj₁ Xₖⱼⁱ)
    ...   | yes Xₖⱼ≈σXₖⱼ with chain₂ X l j k σXₗⱼⁱ σXₗⱼ≈AᵢₖXₖⱼ Xₖⱼ≈σXₖⱼ
    ...     | |σXₖⱼ|<|σXₗⱼ| = reduction X k j
        (𝑰-cong Xₖⱼ≈σXₖⱼ Xₖⱼⁱ) (rec (size (σ X k j)) |σXₖⱼ|<|σXₗⱼ|)

    force-Xᶜ : ∀ X → (∀ u v → dᵣ (X u v) (σ X u v) < Hᶜ) → 𝑪ₘ X
    force-Xᶜ X dᵣ<H i j with 𝑪? (X i j)
    ... | yes Xᵢⱼᶜ = Xᵢⱼᶜ
    ... | no  Xᵢⱼⁱ with X i j ≟ σ X i j
    ...   | no  Xᵢⱼ≉σXᵢⱼ = contradiction (<⇒≤ (H<dᵣ Xᵢⱼ≉σXᵢⱼ (inj₁ Xᵢⱼⁱ))) (<⇒≱ (dᵣ<H i j))
    ...   | yes Xᵢⱼ≈σXᵢⱼ with reduction X i j (𝑰-cong Xᵢⱼ≈σXᵢⱼ Xᵢⱼⁱ) (<-wellFounded (size (σ X i j)))
    ...     | k , Hᶜ<dᵣXₖⱼσXₖⱼ = contradiction Hᶜ<dᵣXₖⱼσXₖⱼ (<⇒≯ (dᵣ<H k j))




    dᵣ-strContrOrbitsᶜ : ∀ {X r s i j} → X r s ≉ σ X r s → (Xᵣₛᶜ : 𝑪 (X r s)) (σXᵣₛᶜ : 𝑪 (σ X r s)) → 
                         (∀ u v → dᵣ (X u v) (σ X u v) ≤ dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ) →
                         dᵣ (σ X i j) (σ (σ X) i j) < dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ
    dᵣ-strContrOrbitsᶜ {X} {r} {s} {i} {j}  Xᵣₛ≉σXᵣₛ Xᵣₛᶜ σXᵣₛᶜ dᵣ≤dᵣᶜXᵣₛσXᵣₛ with σ X i j ≟ σ (σ X) i j
    ... | yes σXᵢⱼ≈σ²Xᵢⱼ = n≢0⇒0<n (Xᵣₛ≉σXᵣₛ ∘ dᵣᶜ≡0⇒x≈y Xᵣₛᶜ σXᵣₛᶜ)
    ... | no  σXᵢⱼ≉σ²Xᵢⱼ with force-Xᶜ X (λ u v → <-transʳ (dᵣ≤dᵣᶜXᵣₛσXᵣₛ u v) (dᵣᶜ<Hᶜ _ _)) 
    ...   | Xᶜ with σ-pres-𝑪ₘ Xᶜ
    ...     | σXᶜ with σ-pres-𝑪ₘ σXᶜ
    ...       | σ²Xᶜ with 𝑪? (σ X i j) | 𝑪? (σ (σ X) i j)
    ...         | no  σXᵢⱼⁱ | _           = contradiction (σXᶜ i j) σXᵢⱼⁱ 
    ...         | yes _     | no  σ²Xᵢⱼⁱ  = contradiction (σ²Xᶜ i j) σ²Xᵢⱼⁱ
    ...         | yes σXᵢⱼᶜ  | yes σ²Xᵢⱼᶜ  = begin
      dᵣᶜ σXᵢⱼᶜ σ²Xᵢⱼᶜ          ≡⟨ dᵣᶜ-cong _ _ _ _ ≈-refl ≈-refl ⟩
      dᵣᶜ (σXᶜ i j) (σ²Xᶜ i j) <⟨ dᵣᶜ-strContr Xᵣₛ≉σXᵣₛ Xᶜ σXᶜ σXᶜ σ²Xᶜ dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ i j ⟩
      dᵣᶜ (Xᶜ r s) (σXᶜ r s)   ≡⟨ dᵣᶜ-cong _ _ _ _ ≈-refl ≈-refl ⟩
      dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ           ∎
      where

      open ≤-Reasoning

      dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ : ∀ {u v} → X u v ≉ σ X u v → dᵣᶜ (Xᶜ u v) (σXᶜ u v) ≤ dᵣᶜ (Xᶜ r s) (σXᶜ r s)
      dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ {u} {v} Xᵤᵥ≉σXᵤᵥ = begin
        dᵣᶜ (Xᶜ u v) (σXᶜ u v) ≤⟨ dᵣᶜ≤dᵣ Xᵤᵥ≉σXᵤᵥ _ _ ⟩
        dᵣ (X u v) (σ X u v)  ≤⟨ dᵣ≤dᵣᶜXᵣₛσXᵣₛ u v ⟩
        dᵣᶜ Xᵣₛᶜ σXᵣₛᶜ         ≡⟨ dᵣᶜ-cong _ _ _ _ ≈-refl ≈-refl ⟩
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
               (∀ u v → dᵣ (X u v) (Y u v) ≤ dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ)
               → 𝑪ₘ Y
    force-Yᶜ {X} {Y} Xᶜ Xᵣₛᶜ Yᵣₛᶜ dᵣ≤dᵣᶜXᵣₛYᵣₛ i j with X i j ≟ Y i j
    ... | yes Xᵢⱼ≈Yᵢⱼ = 𝑪-cong Xᵢⱼ≈Yᵢⱼ (Xᶜ i j)
    ... | no  Xᵢⱼ≉Yᵢⱼ with 𝑪? (Y i j)
    ...   | yes Yᵢⱼᶜ = Yᵢⱼᶜ
    ...   | no  Yᵢⱼⁱ = contradiction (dᵣ≤dᵣᶜXᵣₛYᵣₛ i j) (<⇒≱ (dᵣᶜ<dᵣ Xᵣₛᶜ Yᵣₛᶜ Xᵢⱼ≉Yᵢⱼ (inj₂ Yᵢⱼⁱ)))
    
    dᵣ-strContrᶜᶜ : ∀ {X Y r s} → X r s ≉ Y r s → 𝑪ₘ X →
                    (Xᵣₛᶜ : 𝑪 (X r s)) (Yᵣₛᶜ : 𝑪 (Y r s)) → 
                    (∀ u v → dᵣ (X u v) (Y u v) ≤ dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ) →
                    ∀ i j → dᵣ (σ X i j) (σ Y i j) < dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ
    dᵣ-strContrᶜᶜ {X} {Y} {r} {s}  Xᵣₛ≉Yᵣₛ Xᶜ Xᵣₛᶜ Yᵣₛᶜ dᵣ≤dᵣᶜXᵣₛYᵣₛ i j
      with σ X i j ≟ σ Y i j
    ... | yes σXᵢⱼ≈σYᵢⱼ = n≢0⇒0<n (Xᵣₛ≉Yᵣₛ ∘ dᵣᶜ≡0⇒x≈y Xᵣₛᶜ Yᵣₛᶜ)
    ... | no  σXᵢⱼ≉σYᵢⱼ with force-Yᶜ Xᶜ Xᵣₛᶜ Yᵣₛᶜ dᵣ≤dᵣᶜXᵣₛYᵣₛ 
    ...   | Yᶜ with σ-pres-𝑪ₘ Xᶜ |  σ-pres-𝑪ₘ Yᶜ
    ...       | σXᶜ | σYᶜ with 𝑪? (σ X i j) | 𝑪? (σ Y i j)
    ...         | no  σXᵢⱼⁱ | _         = contradiction (σXᶜ i j) σXᵢⱼⁱ 
    ...         | yes _     | no  σYᵢⱼⁱ = contradiction (σYᶜ i j) σYᵢⱼⁱ
    ...         | yes σXᵢⱼᶜ | yes σYᵢⱼᶜ = begin
      dᵣᶜ σXᵢⱼᶜ σYᵢⱼᶜ         ≡⟨ dᵣᶜ-cong _ _ _ _ ≈-refl ≈-refl ⟩
      dᵣᶜ (σXᶜ i j) (σYᶜ i j) <⟨ dᵣᶜ-strContr Xᵣₛ≉Yᵣₛ Xᶜ Yᶜ σXᶜ σYᶜ dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ i j ⟩
      dᵣᶜ (Xᶜ r s) (Yᶜ r s)   ≡⟨ dᵣᶜ-cong _ _ _ _ ≈-refl ≈-refl ⟩
      dᵣᶜ Xᵣₛᶜ Yᵣₛᶜ           ∎
      where

      open ≤-Reasoning

      dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ : ∀ {u v} → X u v ≉ Y u v →
                       dᵣᶜ (Xᶜ u v) (Yᶜ u v) ≤ dᵣᶜ (Xᶜ r s) (Yᶜ r s)
      dᵣᶜ≤dᵣᶜXᵣₛσXᵣₛ {u} {v} Xᵤᵥ≉Yᵤᵥ = begin
        dᵣᶜ (Xᶜ u v) (Yᶜ u v) ≤⟨ dᵣᶜ≤dᵣ Xᵤᵥ≉Yᵤᵥ _ _ ⟩
        dᵣ  (X u v)  (Y u v)  ≤⟨ dᵣ≤dᵣᶜXᵣₛYᵣₛ u v ⟩
        dᵣᶜ Xᵣₛᶜ     Yᵣₛᶜ     ≡⟨ dᵣᶜ-cong _ _ _ _ ≈-refl ≈-refl ⟩
        dᵣᶜ (Xᶜ r s) (Yᶜ r s) ∎
       
    dᵣ-strContrᶜⁱ : ∀ {X Y : RMatrix} {r s} → 𝑪ₘ X → 𝑰 (Y r s)
                    → (∀ u v → dᵣ (X u v) (Y u v) ≤ Hᶜ + dᵣⁱ (X r s) (Y r s))
                    → ∀ i j → dᵣ (σ X i j) (σ Y i j) < Hᶜ + dᵣⁱ (X r s) (Y r s)
    dᵣ-strContrᶜⁱ {X} {Y} {r} {s} Xᶜ Yᵣₛⁱ dᵣ≤Hᶜ+dᵣⁱ i j with σ X i j ≟ σ Y i j
    ... | yes σXᵢⱼ≈σYᵢⱼ = s≤s z≤n
    ... | no  σXᵢⱼ≉σYᵢⱼ with 𝑪? (σ X i j) | 𝑪? (σ Y i j)
    ...   | yes σXᵢⱼᶜ | yes σYᵢⱼᶜ = dᵣᶜ<Hᶜ+x σXᵢⱼᶜ σYᵢⱼᶜ _
    ...   | yes _     | no  σYᵢⱼⁱ = +-monoʳ-< Hᶜ (dᵣⁱ-strContrᶜ X Y Xᶜ (dᵣ-force-dᵣⁱ X Y dᵣ≤Hᶜ+dᵣⁱ) σYᵢⱼⁱ)
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
