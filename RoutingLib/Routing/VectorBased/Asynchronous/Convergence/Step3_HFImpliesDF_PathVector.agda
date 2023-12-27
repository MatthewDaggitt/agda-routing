
open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Data.Product using (_×_; _,_)
open import Function.Base using (_∘_)
open import Function.Metric.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Nat.Properties

open import RoutingLib.Routing.Prelude as Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions
import RoutingLib.Routing.Algebra.Construct.Consistent as Consistent

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  {A : AdjacencyMatrix algebra n}
  (open Consistent isRoutingAlgebra isPathAlgebra A)
  (distanceFunctionᶜ : RouteDistanceFunction algebraᶜ Aᶜ)
  where

open ≤-Reasoning

open import RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra isRoutingAlgebra isPathAlgebra

open Routing algebra n
open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra

module DV = RouteDistanceFunction distanceFunctionᶜ

open import RoutingLib.Routing.VectorBased.Synchronous algebraᶜ Aᶜ
  using () renaming (F to Fᶜ; F-cong to Fᶜ-cong)

private
  variable
    w x y z : PathWeight
    i j : Fin n

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Height of inconsistent path-weights
hⁱ : PathWeight → ℕ
hⁱ x with 𝑪? x
... | yes _ = 1
... | no  _ = 1 + (suc n ∸ size x)

-- Distance between inconsistent path-weights
rⁱ : PathWeight → PathWeight → ℕ
rⁱ x y = hⁱ x ⊔ hⁱ y

-- Distance between consistent path-weights
rᶜ : Node → ∀ {x y} → 𝑪 x → 𝑪 y → ℕ
rᶜ i xᶜ yᶜ = DV.r i (toCPathWeight xᶜ) (toCPathWeight yᶜ)

-- Distance between path-weights
r : Node → PathWeight → PathWeight → ℕ
r i x y with x ≟ y | 𝑪? x | 𝑪? y
... | yes _ | _      | _      = zero
... | no  _ | yes xᶜ | yes yᶜ = rᶜ i xᶜ yᶜ
... | no  _ | _      | _      = suc DV.rₘₐₓ + rⁱ x y

------------------------------------------------------------------------
-- Properties of hⁱ
------------------------------------------------------------------------

Hⁱ : ℕ
Hⁱ = 2 + n

hⁱ-cong : x ≈ y → hⁱ x ≡ hⁱ y
hⁱ-cong {x} {y} x≈y with 𝑪? x | 𝑪? y
... | yes _  | yes _  = refl
... | no  xⁱ | yes yᶜ = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
... | yes xᶜ | no  yⁱ = contradiction (𝑪-cong x≈y xᶜ) yⁱ
... | no  _  | no  _  = cong (λ v → 1 + (suc n ∸ v)) (size-cong x≈y)

hⁱ-mono : 𝑰 x → 𝑰 y → size x < size y → hⁱ y < hⁱ x
hⁱ-mono {x} {y} xⁱ yⁱ |x|<|y| with 𝑪? x | 𝑪? y
... | yes xᶜ | _      = contradiction xᶜ xⁱ
... | no  _  | yes yᶜ = contradiction yᶜ yⁱ
... | no  _  | no  _  = s≤s (∸-monoʳ-< |x|<|y| (≤-trans (size≤n y) (n≤1+n n)))

hⁱ-decr : 𝑰 (A i j ▷ x) → hⁱ (A i j ▷ x) < hⁱ x
hⁱ-decr Aᵢⱼxⁱ = hⁱ-mono (▷-forces-𝑰 Aᵢⱼxⁱ) Aᵢⱼxⁱ (≤-reflexive (sizeⁱ-incr Aᵢⱼxⁱ))

1≤hⁱ : ∀ x → 1 ≤ hⁱ x
1≤hⁱ x with 𝑪? x
... | yes _ = s≤s z≤n
... | no  _ = s≤s z≤n

hⁱ≤Hⁱ : ∀ x → hⁱ x ≤ Hⁱ
hⁱ≤Hⁱ x with 𝑪? x
... | yes _ = s≤s z≤n
... | no  _ = s≤s (m∸n≤m (suc n) (size x))

h[yᶜ]≤h[x] : 𝑪 y → ∀ x → hⁱ y ≤ hⁱ x
h[yᶜ]≤h[x] {y} yᶜ x with 𝑪? y
... | no yⁱ  = contradiction yᶜ yⁱ
... | yes _  = 1≤hⁱ x

h[yᶜ]<h[xⁱ] : 𝑪 y → 𝑰 x → hⁱ y < hⁱ x
h[yᶜ]<h[xⁱ] {y} {x} yᶜ xⁱ with 𝑪? y | 𝑪? x
... | no yⁱ | _      = contradiction yᶜ yⁱ
... | _     | yes xᶜ = contradiction xᶜ xⁱ
... | yes _ | no  _  = s≤s (m<n⇒0<n∸m (s≤s (size≤n x)))

hⁱ-force-𝑰 : 𝑰 x ⊎ 𝑰 y → hⁱ x ≤ hⁱ y → 𝑰 y
hⁱ-force-𝑰 (inj₂ yⁱ) hx≤hy yᶜ = yⁱ yᶜ
hⁱ-force-𝑰 (inj₁ xⁱ) hx≤hy yᶜ = contradiction (h[yᶜ]<h[xⁱ] yᶜ xⁱ) (≤⇒≯ hx≤hy)

------------------------------------------------------------------------
-- Properties of rⁱ
------------------------------------------------------------------------

rⁱ-cong : rⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
rⁱ-cong x≈y u≈v = cong₂ _⊔_ (hⁱ-cong x≈y) (hⁱ-cong u≈v)

rⁱ-sym : ∀ x y → rⁱ x y ≡ rⁱ y x
rⁱ-sym x y = ⊔-comm (hⁱ x) (hⁱ y)

rⁱ≡0⇒x≈y : rⁱ x y ≡ 0 → x ≈ y
rⁱ≡0⇒x≈y {x} {y} rⁱ≡0 = contradiction rⁱ≡0 (m<n⇒n≢0 (m≤n⇒m≤o⊔n (hⁱ x) (1≤hⁱ y)))

1≤rⁱ : ∀ x y → 1 ≤ rⁱ x y
1≤rⁱ x y = m≤n⇒m≤n⊔o (hⁱ y) (1≤hⁱ x)

rⁱ≤Hⁱ : ∀ x y → rⁱ x y ≤ Hⁱ
rⁱ≤Hⁱ x y = n≤m×o≤m⇒n⊔o≤m (hⁱ≤Hⁱ x) (hⁱ≤Hⁱ y)

rⁱ-bounded : Bounded rⁱ
rⁱ-bounded = Hⁱ , rⁱ≤Hⁱ

rⁱxⁱyᶜ≡hⁱxⁱ : 𝑰 x → 𝑪 y → rⁱ x y ≡ hⁱ x
rⁱxⁱyᶜ≡hⁱxⁱ {x} {y} xⁱ yᶜ with x ≟ y
... | yes x≈y = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
... | no  _   with 𝑪? x | 𝑪? y
...   | yes xᶜ | _     = contradiction xᶜ xⁱ
...   | no  _  | no yⁱ = contradiction yᶜ yⁱ
...   | no  _  | yes _ = cong suc (⊔-identityʳ (suc n ∸ size x))

rⁱxᶜyⁱ≡hⁱyⁱ : 𝑪 x → 𝑰 y → rⁱ x y ≡ hⁱ y
rⁱxᶜyⁱ≡hⁱyⁱ xᶜ yⁱ = trans (rⁱ-sym _ _) (rⁱxⁱyᶜ≡hⁱxⁱ yⁱ xᶜ)

xⁱyᶜzᶜ⇒rⁱxz≤rⁱxy : 𝑰 x → 𝑪 y → 𝑪 z → rⁱ x z ≤ rⁱ x y
xⁱyᶜzᶜ⇒rⁱxz≤rⁱxy xⁱ yᶜ zᶜ =
  ≤-reflexive (trans (rⁱxⁱyᶜ≡hⁱxⁱ xⁱ zᶜ) (sym (rⁱxⁱyᶜ≡hⁱxⁱ xⁱ yᶜ)))

xᶜyᶜzⁱ⇒rⁱxz≤rⁱyz : 𝑪 x → 𝑪 y → 𝑰 z → rⁱ x z ≤ rⁱ y z
xᶜyᶜzⁱ⇒rⁱxz≤rⁱyz {x} {y} {z} xᶜ yᶜ zⁱ =
  subst₂ _≤_ (rⁱ-sym z x) (rⁱ-sym z y) (xⁱyᶜzᶜ⇒rⁱxz≤rⁱxy zⁱ yᶜ xᶜ)

------------------------------------------------------------------------
-- Properties of rᶜ
------------------------------------------------------------------------

Hᶜ : ℕ
Hᶜ = suc DV.rₘₐₓ

module _ (i : Node) where

  rᶜ-cong : (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
             w ≈ y → x ≈ z → rᶜ i wᶜ xᶜ ≡ rᶜ i yᶜ zᶜ
  rᶜ-cong wᶜ xᶜ yᶜ zᶜ w≈y x≈z = DV.cong i
    {x = toCPathWeight wᶜ} {y = toCPathWeight yᶜ}
    {u = toCPathWeight xᶜ} {v = toCPathWeight zᶜ} w≈y x≈z

  x≈y⇒rᶜ≡0 : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → x ≈ y → rᶜ i xᶜ yᶜ ≡ 0
  x≈y⇒rᶜ≡0 xᶜ yᶜ x≈y = DV.≈⇒0 i {toCPathWeight xᶜ} {toCPathWeight yᶜ} x≈y

  rᶜ≡0⇒x≈y : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ i xᶜ yᶜ ≡ 0 → x ≈ y
  rᶜ≡0⇒x≈y xᶜ yᶜ d≡0 = DV.0⇒≈ i {toCPathWeight xᶜ} {toCPathWeight yᶜ} d≡0

  rᶜ<Hᶜ : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ i xᶜ yᶜ < Hᶜ
  rᶜ<Hᶜ xᶜ yᶜ = s≤s (DV.r≤rₘₐₓ i (toCPathWeight xᶜ) (toCPathWeight yᶜ))

  rᶜ<Hᶜ+x : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) z → rᶜ i xᶜ yᶜ < Hᶜ + z
  rᶜ<Hᶜ+x xᶜ yᶜ z = <-≤-trans (rᶜ<Hᶜ xᶜ yᶜ) (m≤m+n Hᶜ z)

  Hᶜ<Hᶜ+rⁱ : ∀ x y → Hᶜ < Hᶜ + rⁱ x y
  Hᶜ<Hᶜ+rⁱ x y = begin
    1 + Hᶜ       ≡⟨ +-comm 1 Hᶜ ⟩
    Hᶜ + 1       ≤⟨ +-monoʳ-≤ Hᶜ (1≤rⁱ x y) ⟩
    Hᶜ + rⁱ x y ∎

------------------------------------------------------------------------
-- Properties of r
------------------------------------------------------------------------

  r-cong : (r i) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
  r-cong {W} {X} {Y} {Z} W≈X Y≈Z with W ≟ Y | X ≟ Z
  ... | yes _   | yes _   = refl
  ... | yes W≈Y | no  X≉Z = contradiction (≈-trans (≈-trans (≈-sym W≈X) W≈Y) Y≈Z) X≉Z
  ... | no  W≉Y | yes X≈Z = contradiction (≈-trans (≈-trans W≈X X≈Z) (≈-sym Y≈Z)) W≉Y
  ... | no _    | no _    with 𝑪? W | 𝑪? X | 𝑪? Y | 𝑪? Z
  ...   | no  Wⁱ | yes Xᶜ | _      | _      = contradiction (𝑪-cong (≈-sym W≈X) Xᶜ) Wⁱ
  ...   | yes Wᶜ | no  Xⁱ | _      |  _     = contradiction (𝑪-cong W≈X Wᶜ) Xⁱ
  ...   | _      | _      | yes Yᶜ | no  Zⁱ = contradiction (𝑪-cong Y≈Z Yᶜ) Zⁱ
  ...   | _      | _      | no  Yⁱ | yes Zᶜ = contradiction (𝑪-cong (≈-sym Y≈Z) Zᶜ) Yⁱ
  ...   | no _   | no _   | _      | _      = cong (Hᶜ +_) (rⁱ-cong W≈X Y≈Z)
  ...   | yes _  | yes _  | no  _  | no  _  = cong (Hᶜ +_) (rⁱ-cong W≈X Y≈Z)
  ...   | yes wᶜ | yes xᶜ  | yes yᶜ | yes zᶜ = rᶜ-cong wᶜ yᶜ xᶜ zᶜ W≈X Y≈Z

  x≈y⇒r≡0 : ∀ {X Y} → X ≈ Y → r i X Y ≡ 0
  x≈y⇒r≡0 {X} {Y} X≈Y with X ≟ Y
  ... | yes _   = refl
  ... | no  X≉Y = contradiction X≈Y X≉Y

  r≡0⇒x≈y : ∀ {X Y} → r i X Y ≡ 0 → X ≈ Y
  r≡0⇒x≈y {X} {Y} r≡0 with X ≟ Y
  ... | yes X≈Y = X≈Y
  ... | no  _   with 𝑪? X | 𝑪? Y
  ...   | yes Xᶜ | yes Yᶜ  = rᶜ≡0⇒x≈y Xᶜ Yᶜ r≡0
  ...   | no  Xⁱ | _      = contradiction r≡0 λ()
  ...   | yes Xᶜ | no  Yⁱ = contradiction r≡0 λ()

  r≤Hᶜ+Hⁱ : ∀ x y → r i x y ≤ Hᶜ + Hⁱ
  r≤Hᶜ+Hⁱ x y with x ≟ y
  ... | yes _ = z≤n
  ... | no  _ with 𝑪? x | 𝑪? y
  ...   | no  _  | no  _  = +-monoʳ-≤ Hᶜ (rⁱ≤Hⁱ x y)
  ...   | no  _  | yes _  = +-monoʳ-≤ Hᶜ (rⁱ≤Hⁱ x y)
  ...   | yes _  | no  _  = +-monoʳ-≤ Hᶜ (rⁱ≤Hⁱ x y)
  ...   | yes xᶜ | yes yᶜ = ≤-trans (<⇒≤ (rᶜ<Hᶜ xᶜ yᶜ)) (m≤m+n Hᶜ Hⁱ)

  r-bounded : Bounded (r i)
  r-bounded = Hᶜ + Hⁱ , r≤Hᶜ+Hⁱ

  r-isProtoMetric : IsProtoMetric _≈_ (r i)
  r-isProtoMetric = record
    { isPartialOrder  = ≤-isPartialOrder
    ; nonNegative     = z≤n
    ; ≈-isEquivalence = ≈-isEquivalence
    ; cong            = r-cong
    }

  r-isPreMetric : IsPreMetric _≈_ (r i)
  r-isPreMetric = record
    { isProtoMetric = r-isProtoMetric
    ; ≈⇒0           = x≈y⇒r≡0
    }

  r-isQuasiSemiMetric : IsQuasiSemiMetric _≈_ (r i)
  r-isQuasiSemiMetric = record
    { isPreMetric = r-isPreMetric
    ; 0⇒≈         = r≡0⇒x≈y
    }

  H<r : x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ < r i x y
  H<r {x} {y} x≉y xⁱ⊎yⁱ with x ≟ y
  ... | yes x≈y = contradiction x≈y x≉y
  ... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
  ... | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
  ... | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ
  ... | no  _  | _      | _       = Hᶜ<Hᶜ+rⁱ x y
  ... | yes _  | no  _  | _       = Hᶜ<Hᶜ+rⁱ x y

  rᶜ<r : ∀ (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) → y ≉ z → 𝑰 y ⊎ 𝑰 z  → rᶜ i wᶜ xᶜ < r i y z
  rᶜ<r wᶜ xᶜ y≉z yⁱ⊎zⁱ = ≤-<-trans (<⇒≤ (rᶜ<Hᶜ wᶜ xᶜ)) (H<r y≉z yⁱ⊎zⁱ)

  rᶜ≤r : x ≉ y → (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ i xᶜ yᶜ ≤ r i x y
  rᶜ≤r {x} {y} x≉y xᶜ yᶜ with x ≟ y
  ... | yes x≈y = contradiction x≈y x≉y
  ... | no  _ with 𝑪? x | 𝑪? y
  ...   | no  xⁱ  | _       = contradiction xᶜ xⁱ
  ...   | yes _   | no  yⁱ  = contradiction yᶜ yⁱ
  ...   | yes xᶜ' | yes yᶜ' = ≤-reflexive (DV.cong i ≈-refl ≈-refl)

  rᶜ≡r : ∀ {p q} (pᶜ : 𝑪 p) (qᶜ : 𝑪 q) → x ≈ p → y ≈ q → rᶜ i pᶜ qᶜ ≡ r i x y
  rᶜ≡r {x} {y} {p} {q} pᶜ qᶜ x≈p y≈q with x ≟ y | 𝑪? x | 𝑪? y
  ... | yes x≈y | _      | _      = DV.≈⇒0 i (≈-trans (≈-trans (≈-sym x≈p) x≈y) y≈q)
  ... | _       | no  xⁱ | _      = contradiction (𝑪-cong (≈-sym x≈p) pᶜ) xⁱ
  ... | _       | _      | no  yⁱ = contradiction (𝑪-cong (≈-sym y≈q) qᶜ) yⁱ
  ... | no _    | yes xᶜ | yes yᶜ = rᶜ-cong pᶜ qᶜ xᶜ yᶜ (≈-sym x≈p) (≈-sym y≈q)

  H+rⁱ≡r : w ≈ x → z ≈ y → x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ + rⁱ w z ≡ r i x y
  H+rⁱ≡r {w} {x} {z} {y} w≈x z≈y x≉y xⁱ⊎yⁱ with x ≟ y
  ... | yes x≈y = contradiction x≈y x≉y
  ... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
  ...   | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
  ...   | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ
  ...   | no  _  | _      | _       = cong (Hᶜ +_) (rⁱ-cong w≈x z≈y)
  ...   | yes _  | no  _  | _       = cong (Hᶜ +_) (rⁱ-cong w≈x z≈y)

r-force-rⁱ : ∀ (X Y : RoutingMatrix) {i j} →
              (∀ u v → r u (X u v) (Y u v) ≤ Hᶜ + rⁱ (X i j) (Y i j)) →
              (∀ {u v} → X u v ≉ Y u v → 𝑰 (X u v) ⊎ 𝑰 (Y u v) →
               rⁱ (X u v) (Y u v) ≤ rⁱ (X i j) (Y i j))
r-force-rⁱ X Y {i} {j} r≤Hᶜ+rⁱXₗYₗ {u} {v} Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ = +-cancelˡ-≤ Hᶜ _ _ (begin
  Hᶜ + rⁱ (X u v) (Y u v) ≡⟨ H+rⁱ≡r u ≈-refl ≈-refl Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ ⟩
  r u (X u v) (Y u v)     ≤⟨ r≤Hᶜ+rⁱXₗYₗ u v ⟩
  Hᶜ + rⁱ (X i j) (Y i j) ∎)
  
------------------------------------------------------------------------
-- r is strictly contracting
------------------------------------------------------------------------

open import RoutingLib.Routing.VectorBased.Synchronous algebra A hiding (_≈ₘ_)
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Properties as PathVectorProperties

open PathVectorProperties isRoutingAlgebra isPathAlgebra A

rⁱ-strContrOrbits-FX : ∀ {X i j} → 𝑰 (F X i j) →
                        ∀ {v} → (∀ k l → r k (X k l) (F X k l) ≤ v) →
                        Hᶜ + hⁱ (F X i j) < v
rⁱ-strContrOrbits-FX {X} {i} {j} FXᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X i j FXᵢⱼⁱ
... | (k , Xₖⱼ≉FXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|FXᵢⱼ|) = begin-strict
  Hᶜ + hⁱ (F X i j)                 <⟨ +-monoʳ-< Hᶜ (hⁱ-mono Xₖⱼⁱ FXᵢⱼⁱ |Xₖⱼ|<|FXᵢⱼ|) ⟩
  Hᶜ + hⁱ (X k j)                   ≤⟨ +-monoʳ-≤ Hᶜ (m≤m⊔n _ _) ⟩
  Hᶜ + (hⁱ (X k j) ⊔ hⁱ (F X k j))  ≡⟨ H+rⁱ≡r k ≈-refl ≈-refl Xₖⱼ≉FXₖⱼ (inj₁ Xₖⱼⁱ) ⟩
  r k (X k j) (F X k j)             ≤⟨ r≤v k j ⟩
  v                                 ∎

rⁱ-strContrOrbits-F²X : ∀ {X i j} → 𝑰 (F (F X) i j) →
                         ∀ {v} → (∀ k l → r k (X k l) (F X k l) ≤ v) →
                         Hᶜ + hⁱ (F (F X) i j) < v
rⁱ-strContrOrbits-F²X {X} {i} {j} F²Xᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ (F X) i j F²Xᵢⱼⁱ
... | (l , _ , FXₗⱼⁱ , |FXₗⱼ|<|F²Xₗⱼ|) with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X l j FXₗⱼⁱ
...   | (k , Xₖⱼ≉FXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|FXₖⱼ|) = begin-strict
  Hᶜ + hⁱ (F (F X) i j)             <⟨ +-monoʳ-< Hᶜ (hⁱ-mono Xₖⱼⁱ F²Xᵢⱼⁱ (<-trans |Xₖⱼ|<|FXₖⱼ| |FXₗⱼ|<|F²Xₗⱼ|)) ⟩
  Hᶜ + hⁱ (X k j)                   ≤⟨ +-monoʳ-≤ Hᶜ (m≤m⊔n _ _) ⟩
  Hᶜ + (hⁱ (X k j) ⊔ hⁱ (F X k j))  ≡⟨ H+rⁱ≡r k ≈-refl ≈-refl Xₖⱼ≉FXₖⱼ (inj₁ Xₖⱼⁱ) ⟩
  r k (X k j) (F X k j)             ≤⟨ r≤v k j ⟩
  v                                 ∎

rⁱ-strContrOn𝑪 : ∀ {X Y i j} → 𝑪ₘ X → 𝑰 (F Y i j) →
                  ∀ {v} → (∀ k l → r k (X k l) (Y k l) ≤ v) →
                  Hᶜ + rⁱ (F X i j) (F Y i j) < v
rⁱ-strContrOn𝑪 {X} {Y} {i} {j} Xᶜ FYᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ Y i j FYᵢⱼⁱ
... | (k , FYᵢⱼ≈AᵢₖYₖⱼ , Yₖⱼⁱ) = begin-strict
  Hᶜ + rⁱ (F X i j) (F Y i j)  ≡⟨ cong (Hᶜ +_) (rⁱxᶜyⁱ≡hⁱyⁱ (F-pres-𝑪ₘ Xᶜ i j) FYᵢⱼⁱ) ⟩
  Hᶜ + hⁱ (F Y i j)            ≡⟨ cong (Hᶜ +_) (hⁱ-cong FYᵢⱼ≈AᵢₖYₖⱼ) ⟩
  Hᶜ + hⁱ (A i k ▷ Y k j)      <⟨ +-monoʳ-< Hᶜ (hⁱ-decr (𝑰-cong FYᵢⱼ≈AᵢₖYₖⱼ FYᵢⱼⁱ)) ⟩
  Hᶜ + hⁱ (Y k j)              ≡⟨ cong (Hᶜ +_) (sym (rⁱxᶜyⁱ≡hⁱyⁱ (Xᶜ k j) Yₖⱼⁱ)) ⟩
  Hᶜ + rⁱ (X k j) (Y k j)      ≡⟨ H+rⁱ≡r k ≈-refl ≈-refl (𝑪𝑰⇒≉ (Xᶜ k j) Yₖⱼⁱ) (inj₂ Yₖⱼⁱ) ⟩
  r k (X k j) (Y k j)          ≤⟨ r≤v k j ⟩
  v                            ∎

rⁱ-strContrOrbits : ∀ {X i j} → 𝑰 (F X i j) ⊎ 𝑰 (F (F X) i j) →
                     ∀ {v} → (∀ k l → r k (X k l) (F X k l) ≤ v) →
                     Hᶜ + rⁱ (F X i j) (F (F X) i j) < v
rⁱ-strContrOrbits {X} {i} {j} FXᵢⱼⁱ⊎F²Xᵢⱼⁱ {v} r≤v with ≤-total (hⁱ (F X i j)) (hⁱ (F (F X) i j))
... | inj₁ hⁱFXᵢⱼ≤hⁱF²Xᵢⱼ = subst (_< v) (sym (cong (Hᶜ +_) (m≤n⇒m⊔n≡n hⁱFXᵢⱼ≤hⁱF²Xᵢⱼ))) (rⁱ-strContrOrbits-F²X (hⁱ-force-𝑰 FXᵢⱼⁱ⊎F²Xᵢⱼⁱ hⁱFXᵢⱼ≤hⁱF²Xᵢⱼ) r≤v)
... | inj₂ hⁱF²Xᵢⱼ≤hⁱFXᵢⱼ = subst (_< v) (sym (cong (Hᶜ +_) (m≥n⇒m⊔n≡m hⁱF²Xᵢⱼ≤hⁱFXᵢⱼ))) (rⁱ-strContrOrbits-FX {X} {i} {j} (hⁱ-force-𝑰 (swap FXᵢⱼⁱ⊎F²Xᵢⱼⁱ) hⁱF²Xᵢⱼ≤hⁱFXᵢⱼ) r≤v)

------------------------------------------------------------------------
-- rᶜ is contracting in the right way

rᶜ-strContrOrbits-𝑪𝑪 : ∀ {X} (Xᶜ : 𝑪ₘ X) →
                       ∀ {i j} (FXᵢⱼᶜ : 𝑪 (F X i j)) (F²Xᵢⱼᶜ : 𝑪 (F (F X) i j)) →
                       ∀ {v} → 0 < v → (∀ k l → r k (X k l) (F X k l) ≤ v) →
                       rᶜ i FXᵢⱼᶜ F²Xᵢⱼᶜ < v
rᶜ-strContrOrbits-𝑪𝑪 {X} Xᶜ {i} {j} FXᵢⱼᶜ F²Xᵢⱼᶜ {v} 0<v r≤v = begin-strict
  rᶜ   i FXᵢⱼᶜ       F²Xᵢⱼᶜ            ≡⟨⟩
  DV.r i (cFX i j)   (cF²X i j)        ≡⟨ DV.cong i (cFX≈FcX i j) cF²X≈F²cX ⟩
  DV.r i (Fᶜ cX i j) (Fᶜ (Fᶜ cX) i j)  <⟨ DV.r-strContrOrbits 0<v d≤v i j  ⟩
  v                                    ∎
  where
  FXᶜ = F-pres-𝑪ₘ Xᶜ
  F²Xᶜ = F-pres-𝑪ₘ FXᶜ
  cX  = toCMatrix Xᶜ
  cFX = toCMatrix FXᶜ
  cF²X = toCMatrix F²Xᶜ
  cFX≈FcX = F-toCMatrix-commute′ Xᶜ
  cF²X≈F²cX = ≈-trans (F-toCMatrix-commute′ FXᶜ i j) (Fᶜ-cong {X = cFX} {Y = Fᶜ cX} cFX≈FcX i j)
  
  d≤v : ∀ k j → DV.r k (cX k j) (Fᶜ cX k j) ≤ v
  d≤v k j = begin
    DV.r k (cX k j) (Fᶜ cX k j) ≡⟨ DV.cong k ≈-refl (≈-sym (cFX≈FcX k j)) ⟩
    rᶜ   k (Xᶜ k j) (FXᶜ k j)   ≡⟨ rᶜ≡r k (Xᶜ k j) (FXᶜ k j) ≈-refl ≈-refl ⟩
    r    k (X k j)  (F X k j)   ≤⟨ r≤v k j ⟩
    v                           ∎

rᶜ-strContrFP-𝑪𝑪 : ∀ {X*} → F X* ≈ₘ X* → ∀ {X} (Xᶜ : 𝑪ₘ X) →
                   ∀ {i j} (X*ᵢⱼᶜ : 𝑪 (X* i j)) (FXᵢⱼᶜ : 𝑪 (F X i j)) →
                   ∀ {v} → 0 < v → (∀ k l → r k (X* k l) (X k l) ≤ v) →
                   rᶜ i X*ᵢⱼᶜ FXᵢⱼᶜ < v
rᶜ-strContrFP-𝑪𝑪 {X*} FX*≈X* {X} Xᶜ {i} {j} X*ᵢⱼᶜ FXᵢⱼᶜ {v} 0<v r≤v = begin-strict
  rᶜ   i X*ᵢⱼᶜ FXᵢⱼᶜ           ≡⟨⟩
  DV.r i (cX* i j) (cFX i j)   ≡⟨ DV.cong i ≈-refl (cFX≈FcX i j) ⟩
  DV.r i (cX* i j) (Fᶜ cX i j) <⟨ DV.r-strContrFP FᶜX*≈X* 0<v d≤v i j ⟩
  v                            ∎
  where
  X*ᶜ = fixedPointᶜ FX*≈X*
  FXᶜ = F-pres-𝑪ₘ Xᶜ
  cX  = toCMatrix Xᶜ
  cFX = toCMatrix (F-pres-𝑪ₘ Xᶜ)
  cX*  = toCMatrix X*ᶜ
  cFX≈FcX = F-toCMatrix-commute′ Xᶜ
  FᶜX*≈X* = λ i j → ≈-trans (≈-sym (F-toCMatrix-commute′ X*ᶜ i j)) (FX*≈X* i j)

  d≤v : ∀ k l → DV.r k (cX* k l) (cX k l) ≤ v
  d≤v k l = begin
    DV.r k (cX* k l) (cX k l)  ≡⟨⟩
    rᶜ   k (X*ᶜ k l)  (Xᶜ k l) ≡⟨ rᶜ≡r k (X*ᶜ k l) (Xᶜ k l) ≈-refl ≈-refl ⟩
    r    k (X* k l)  (X k l)   ≤⟨ r≤v k l ⟩
    v                          ∎

rᶜ-strContr-𝑪𝑰 : ∀ {X Y i j} → (𝑰ₘ X × 𝑪ₘ Y) ⊎ (𝑪ₘ X × 𝑰ₘ Y) →
                 (FXᵢⱼᶜ : 𝑪 (F X i j)) (FYᵢⱼᶜ : 𝑪 (F Y i j)) →
                 ∀ {v} → (∀ k l → r k (X k l) (Y k l) ≤ v) →
                 rᶜ i FXᵢⱼᶜ FYᵢⱼᶜ < v
rᶜ-strContr-𝑪𝑰 {X} {Y} {i} (inj₁ (Xⁱ , Yᶜ)) FXᵢⱼᶜ FYᵢⱼᶜ {v} r≤v with 𝑰ₘ-witness Xⁱ
...   | (k , l , Xₖₗⁱ) = begin-strict
  rᶜ i FXᵢⱼᶜ  FYᵢⱼᶜ        <⟨ rᶜ<Hᶜ+x i FXᵢⱼᶜ FYᵢⱼᶜ _ ⟩
  Hᶜ + rⁱ (X k l) (Y k l)  ≡⟨ H+rⁱ≡r k ≈-refl ≈-refl (𝑪𝑰⇒≉ (Yᶜ k l) Xₖₗⁱ ∘ ≈-sym) (inj₁ Xₖₗⁱ) ⟩
  r k (X k l) (Y k l)      ≤⟨ r≤v k l ⟩
  v                        ∎
rᶜ-strContr-𝑪𝑰 {X} {Y} {i} (inj₂ (Xᶜ , Yⁱ)) FXᵢⱼᶜ FYᵢⱼᶜ {v} r≤v with 𝑰ₘ-witness Yⁱ
... | (k , l , Yₖₗⁱ) = begin-strict
  rᶜ i FXᵢⱼᶜ  FYᵢⱼᶜ        <⟨ rᶜ<Hᶜ+x i FXᵢⱼᶜ FYᵢⱼᶜ _ ⟩
  Hᶜ + rⁱ (X k l) (Y k l)  ≡⟨ H+rⁱ≡r k ≈-refl ≈-refl (𝑪𝑰⇒≉ (Xᶜ k l) Yₖₗⁱ) (inj₂ Yₖₗⁱ) ⟩
  r k (X k l) (Y k l)      ≤⟨ r≤v k l ⟩
  v                        ∎

rᶜ-strContrOrbits : ∀ {X i j} →
                     (FXᵢⱼᶜ : 𝑪 (F X i j)) (F²Xᵢⱼᶜ : 𝑪 (F (F X) i j)) →
                     ∀ {v} → 0 < v → (∀ k l → r k (X k l) (F X k l) ≤ v) →
                     rᶜ i FXᵢⱼᶜ F²Xᵢⱼᶜ < v
rᶜ-strContrOrbits {X} {i} {j} FXᵢⱼᶜ F²Xᵢⱼᶜ {v} 0<v r≤v with 𝑪ₘ? X | 𝑪ₘ? (F X)
... | yes Xᶜ | yes FXᶜ = rᶜ-strContrOrbits-𝑪𝑪 Xᶜ FXᵢⱼᶜ F²Xᵢⱼᶜ 0<v r≤v
... | yes Xᶜ | no  FXⁱ = contradiction (F-pres-𝑪ₘ Xᶜ) FXⁱ
... | no  Xⁱ | yes FXᶜ = rᶜ-strContr-𝑪𝑰 (inj₁ (Xⁱ , FXᶜ)) FXᵢⱼᶜ F²Xᵢⱼᶜ r≤v
... | no  Xⁱ | no  FXⁱ with 𝑰ₘ-witness FXⁱ
...   | (m , n , FXₘₙⁱ) with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X m n FXₘₙⁱ
...     | (k , Xₖₙ≉FXₖₙ , Xₖₙⁱ , _) = begin-strict
  rᶜ i FXᵢⱼᶜ  F²Xᵢⱼᶜ        <⟨ rᶜ<Hᶜ+x i FXᵢⱼᶜ F²Xᵢⱼᶜ _ ⟩
  Hᶜ + rⁱ (X k n) (F X k n) ≡⟨ H+rⁱ≡r k ≈-refl ≈-refl Xₖₙ≉FXₖₙ (inj₁ Xₖₙⁱ) ⟩
  r k (X k n) (F X k n)     ≤⟨ r≤v k n ⟩
  v                         ∎

rᶜ-strContrFP : ∀ {X*} → F X* ≈ₘ X* →
                ∀ {X i j} → (X*ᵢⱼᶜ : 𝑪 (X* i j)) (FXᵢⱼᶜ : 𝑪 (F X i j)) →
                ∀ {v} → 0 < v → (∀ k l → r k (X* k l) (X k l) ≤ v) →
                rᶜ i X*ᵢⱼᶜ FXᵢⱼᶜ < v
rᶜ-strContrFP {X*} FX*≈X* {X} {i} {j} X*ᵢⱼᶜ FXᵢⱼᶜ {v} 0<v r≤v with 𝑪ₘ? X
... | yes Xᶜ = rᶜ-strContrFP-𝑪𝑪 FX*≈X* Xᶜ X*ᵢⱼᶜ FXᵢⱼᶜ 0<v r≤v
... | no  Xⁱ = begin-strict
  rᶜ i X*ᵢⱼᶜ  FXᵢⱼᶜ ≡⟨ DV.cong i (≈-sym (FX*≈X* i j)) ≈-refl ⟩
  rᶜ i FX*ᵢⱼᶜ FXᵢⱼᶜ <⟨ rᶜ-strContr-𝑪𝑰 (inj₂ (X*ᶜ , Xⁱ)) FX*ᵢⱼᶜ FXᵢⱼᶜ r≤v ⟩
  v                 ∎
  where
  X*ᶜ : 𝑪ₘ X*
  X*ᶜ = fixedPointᶜ FX*≈X*

  FX*ᵢⱼᶜ : 𝑪 (F X* i j)
  FX*ᵢⱼᶜ = F-pres-𝑪ₘ X*ᶜ i j

  
------------------------------------------------------------------------
-- r is contracting in the right way

r-strContrOrbits : ∀ {X} →
                   ∀ {v} → 0 < v → (∀ k l → r k (X k l) (F X k l) ≤ v) →
                   ∀ i j → r i (F X i j) (F (F X) i j) < v
r-strContrOrbits {X} 0<v r≤v i j
  with F X i j ≟ F (F X) i j | 𝑪? (F X i j) | 𝑪? (F (F X) i j)
... | yes FXᵢⱼ≈F²Xᵢⱼ | _         | _          = 0<v
... | no  _          | yes FXᵢⱼᶜ | yes F²Xᵢⱼᶜ = rᶜ-strContrOrbits FXᵢⱼᶜ F²Xᵢⱼᶜ 0<v r≤v
... | no  _          | no  FXᵢⱼⁱ | _          = rⁱ-strContrOrbits (inj₁ FXᵢⱼⁱ) r≤v
... | no  _          | yes _     | no  F²Xᵢⱼⁱ = rⁱ-strContrOrbits (inj₂ F²Xᵢⱼⁱ) r≤v

r-strContrFP : ∀ {X*} → F X* ≈ₘ X* →
               ∀ {X v} → 0 < v → (∀ k l → r k (X* k l) (X k l) ≤ v) →
               ∀ i j → r i (X* i j) (F X i j) < v
r-strContrFP {X*} FX*≈X* {X} {v} 0<v r≤v i j
  with X* i j ≟ F X i j | 𝑪? (X* i j) | 𝑪? (F X i j)
... | yes FXᵢⱼ≈FYᵢⱼ | _         | _         = 0<v
... | no  FXᵢⱼ≉FYᵢⱼ | no  X*ᵢⱼⁱ | _         = contradiction (fixedPointᶜ FX*≈X* i j) X*ᵢⱼⁱ
... | no  FXᵢⱼ≉FYᵢⱼ | yes X*ᵢⱼᶜ | yes FXᵢⱼᶜ = rᶜ-strContrFP FX*≈X* X*ᵢⱼᶜ FXᵢⱼᶜ 0<v r≤v
... | no  FXᵢⱼ≉FYᵢⱼ | yes X*ᵢⱼᶜ | no  FXᵢⱼⁱ = begin-strict
  Hᶜ + rⁱ (X* i j)   (F X i j) ≡⟨ cong (Hᶜ +_) (rⁱ-cong (≈-sym (FX*≈X* i j)) ≈-refl) ⟩
  Hᶜ + rⁱ (F X* i j) (F X i j) <⟨ rⁱ-strContrOn𝑪 (fixedPointᶜ FX*≈X*) FXᵢⱼⁱ r≤v ⟩
  v                            ∎

------------------------------------------------------------------------
-- Route distance function
------------------------------------------------------------------------

routeDistanceFunction : RouteDistanceFunction algebra A
routeDistanceFunction = record
  { r                   = r
  ; r-isQuasiSemiMetric = r-isQuasiSemiMetric
  ; r-bounded           = r-bounded
  ; r-strContrOrbits    = r-strContrOrbits
  ; r-strContrFP        = r-strContrFP
  }
