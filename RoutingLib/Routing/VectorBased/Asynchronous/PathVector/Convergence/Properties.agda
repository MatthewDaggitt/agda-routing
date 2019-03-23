open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Data.Product using (∃; _,_; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Function.Metric.Nat
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Construct.Consistent as Consistent
import RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra as PathAlgebraProperties
import RoutingLib.Routing.Algebra.Properties.FiniteRoutingAlgebra as FiniteRoutingAlgebraProperties
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)

import RoutingLib.Routing.VectorBased.Asynchronous as AsyncVectorBased
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.Metrics as Metrics
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Properties as DistanceVectorMetricProperties

open ≤-Reasoning

module RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.Properties
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  (1≤n : 1 ≤ n) (p : Subset n)
  where

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open PathAlgebraProperties isRoutingAlgebra isPathAlgebra
open Consistent isRoutingAlgebra isPathAlgebra A

open Routing algebra n
open Metrics isRoutingAlgebra isPathAlgebra A
private module DVP = DistanceVectorMetricProperties isRoutingAlgebraᶜ isFiniteᶜ

------------------------------------------------------------------------
-- General properties

1<1+n∸∣x∣ : ∀ {r} → 1 < suc n ∸ size r
1<1+n∸∣x∣ {r} = begin
  2                    ≡⟨ sym (m+n∸n≡m 2 n) ⟩
  2 + n ∸ n            ≤⟨ ∸-monoʳ-≤ (suc (suc n)) (size<n 1≤n r) ⟩
  2 + n ∸ suc (size r) ≡⟨⟩
  1 + n ∸ size r       ∎

------------------------------------------------------------------------
-- Properties of hⁱ

Hⁱ : ℕ
Hⁱ = suc n

hⁱ-cong : ∀ {r s} → r ≈ s → hⁱ r ≡ hⁱ s
hⁱ-cong {r} {s} r≈s with 𝑪? r | 𝑪? s
... | yes _  | yes _  = refl
... | no  rⁱ | yes sᶜ = contradiction (𝑪-cong (≈-sym r≈s) sᶜ) rⁱ
... | yes rᶜ | no  sⁱ = contradiction (𝑪-cong r≈s rᶜ) sⁱ
... | no  _  | no  _  = cong (suc n ∸_) (size-cong r≈s)

hⁱ-mono : ∀ {x y} → 𝑰 x → 𝑰 y → size x < size y → hⁱ y < hⁱ x
hⁱ-mono {x} {y} xⁱ yⁱ |x|<|y| with 𝑪? x | 𝑪? y
... | yes xᶜ | _      = contradiction xᶜ xⁱ
... | no  _  | yes yᶜ = contradiction yᶜ yⁱ
... | no  _  | no  _  = ∸-monoʳ-< |x|<|y| (size≤n+1 _)

hⁱ-decr : ∀ {i j x} → 𝑰 (A i j ▷ x) → hⁱ (A i j ▷ x) < hⁱ x
hⁱ-decr Aᵢⱼxⁱ = hⁱ-mono (▷-forces-𝑰 Aᵢⱼxⁱ) Aᵢⱼxⁱ (≤-reflexive (sizeⁱ-incr Aᵢⱼxⁱ))

1≤hⁱ : ∀ r → 1 ≤ hⁱ r
1≤hⁱ r with 𝑪? r
... | yes _ = s≤s z≤n
... | no  _ = m<n⇒0<n∸m (s≤s (<⇒≤ (size<n 1≤n r)))

hⁱ≤Hⁱ : ∀ r → hⁱ r ≤ Hⁱ
hⁱ≤Hⁱ r with 𝑪? r
... | yes _ = s≤s z≤n
... | no  _ = n∸m≤n (size r) Hⁱ


h[sᶜ]≤h[r] : ∀ {s} → 𝑪 s → ∀ r → hⁱ s ≤ hⁱ r
h[sᶜ]≤h[r] {s} sᶜ r with 𝑪? s
... | no sⁱ  = contradiction sᶜ sⁱ
... | yes _  = 1≤hⁱ r

h[sᶜ]<h[rⁱ] : ∀ {s r} → 𝑪 s → 𝑰 r → hⁱ s < hⁱ r
h[sᶜ]<h[rⁱ] {s} {r} sᶜ rⁱ with 𝑪? s | 𝑪? r
... | no sⁱ | _      = contradiction sᶜ sⁱ
... | _     | yes rᶜ = contradiction rᶜ rⁱ
... | yes _ | no  _  = 1<1+n∸∣x∣

hⁱ-force-𝑰 : ∀ {x y} → 𝑰 x ⊎ 𝑰 y → hⁱ x ≤ hⁱ y → 𝑰 y
hⁱ-force-𝑰 (inj₂ yⁱ) hx≤hy yᶜ = yⁱ yᶜ
hⁱ-force-𝑰 (inj₁ xⁱ) hx≤hy yᶜ = contradiction (h[sᶜ]<h[rⁱ] yᶜ xⁱ) (≤⇒≯ hx≤hy)

------------------------------------------------------------------------
-- Properties of rⁱ

rⁱ-cong : rⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
rⁱ-cong x≈y u≈v = cong₂ _⊔_ (hⁱ-cong x≈y) (hⁱ-cong u≈v)

rⁱ-sym : ∀ x y → rⁱ x y ≡ rⁱ y x
rⁱ-sym x y = ⊔-comm (hⁱ x) (hⁱ y)

rⁱ≡0⇒x≈y : ∀ {x y} → rⁱ x y ≡ 0 → x ≈ y
rⁱ≡0⇒x≈y {x} {y} rⁱ≡0 = contradiction rⁱ≡0 (m<n⇒n≢0 (m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)))

rⁱ-maxTriIneq : MaxTriangleInequality rⁱ
rⁱ-maxTriIneq x y z = begin
  hⁱ x ⊔ hⁱ z                   ≤⟨ ⊔-monoˡ-≤ (hⁱ z) (m≤m⊔n (hⁱ x) (hⁱ y)) ⟩
  hⁱ x ⊔ hⁱ y ⊔ hⁱ z            ≡⟨ ⊔-triangulate (hⁱ x) (hⁱ y) (hⁱ z) ⟩
  (hⁱ x ⊔ hⁱ y) ⊔ (hⁱ y ⊔ hⁱ z) ∎

1≤rⁱ : ∀ x y → 1 ≤ rⁱ x y
1≤rⁱ x y = m≤n⇒m≤n⊔o (hⁱ y) (1≤hⁱ x)

rⁱ≤Hⁱ : ∀ x y → rⁱ x y ≤ Hⁱ
rⁱ≤Hⁱ x y = n≤m×o≤m⇒n⊔o≤m (hⁱ≤Hⁱ x) (hⁱ≤Hⁱ y)

rⁱ-bounded : Bounded rⁱ
rⁱ-bounded = Hⁱ , rⁱ≤Hⁱ

rⁱxⁱyᶜ≡hⁱxⁱ : ∀ {x y} → 𝑰 x → 𝑪 y → rⁱ x y ≡ hⁱ x
rⁱxⁱyᶜ≡hⁱxⁱ {x} {y} xⁱ yᶜ with x ≟ y
... | yes x≈y = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
... | no  _   with 𝑪? x | 𝑪? y
...   | yes xᶜ | _      = contradiction xᶜ xⁱ
...   | no  _  | no yⁱ = contradiction yᶜ yⁱ
...   | no  _  | yes _ = m≤n⇒n⊔m≡n (<⇒≤ 1<1+n∸∣x∣)

rⁱxᶜyⁱ≡hⁱyⁱ : ∀ {x y} → 𝑪 x → 𝑰 y → rⁱ x y ≡ hⁱ y
rⁱxᶜyⁱ≡hⁱyⁱ xᶜ yⁱ = trans (rⁱ-sym _ _) (rⁱxⁱyᶜ≡hⁱxⁱ yⁱ xᶜ)

xⁱyᶜzᶜ⇒rⁱxz≤rⁱxy : ∀ {x y z} → 𝑰 x → 𝑪 y → 𝑪 z → rⁱ x z ≤ rⁱ x y
xⁱyᶜzᶜ⇒rⁱxz≤rⁱxy xⁱ yᶜ zᶜ =
  ≤-reflexive (trans (rⁱxⁱyᶜ≡hⁱxⁱ xⁱ zᶜ) (sym (rⁱxⁱyᶜ≡hⁱxⁱ xⁱ yᶜ)))

xᶜyᶜzⁱ⇒rⁱxz≤rⁱyz : ∀ {x y z} → 𝑪 x → 𝑪 y → 𝑰 z → rⁱ x z ≤ rⁱ y z
xᶜyᶜzⁱ⇒rⁱxz≤rⁱyz {x} {y} {z} xᶜ yᶜ zⁱ =
  subst₂ _≤_ (rⁱ-sym z x) (rⁱ-sym z y) (xⁱyᶜzᶜ⇒rⁱxz≤rⁱxy zⁱ yᶜ xᶜ)

------------------------------------------------------------------------
-- Properties of rᶜ

Hᶜ : ℕ
Hᶜ = suc (FiniteRoutingAlgebraProperties.H isRoutingAlgebraᶜ isFiniteᶜ)

rᶜ-cong : ∀ {x y w z} (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
           w ≈ y → x ≈ z → rᶜ wᶜ xᶜ ≡ rᶜ yᶜ zᶜ
rᶜ-cong wᶜ xᶜ yᶜ zᶜ w≈y x≈z = DVP.r-cong
  {x = toCRoute wᶜ} {y = toCRoute yᶜ}
  {u = toCRoute xᶜ} {v = toCRoute zᶜ} w≈y x≈z

rᶜ-sym : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ ≡ rᶜ yᶜ xᶜ
rᶜ-sym xᶜ yᶜ = DVP.r-sym (toCRoute xᶜ) (toCRoute yᶜ)

x≈y⇒rᶜ≡0 : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → x ≈ y → rᶜ xᶜ yᶜ ≡ 0
x≈y⇒rᶜ≡0 xᶜ yᶜ x≈y = DVP.x≈y⇒r≡0 {toCRoute xᶜ} {toCRoute yᶜ} x≈y

rᶜ≡0⇒x≈y : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ ≡ 0 → x ≈ y
rᶜ≡0⇒x≈y xᶜ yᶜ d≡0 = DVP.r≡0⇒x≈y {toCRoute xᶜ} {toCRoute yᶜ} d≡0

rᶜ-maxTriIneq : ∀ {x y z} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
                rᶜ xᶜ zᶜ ≤ rᶜ xᶜ yᶜ ⊔ rᶜ yᶜ zᶜ
rᶜ-maxTriIneq xᶜ yᶜ zᶜ = DVP.r-maxTriIneq (toCRoute xᶜ) (toCRoute yᶜ) (toCRoute zᶜ)

rᶜ<Hᶜ : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ < Hᶜ
rᶜ<Hᶜ xᶜ yᶜ = s≤s (DVP.r≤H (toCRoute xᶜ) (toCRoute yᶜ))

rᶜ<Hᶜ+x : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) z → rᶜ xᶜ yᶜ < Hᶜ + z
rᶜ<Hᶜ+x xᶜ yᶜ z = <-transˡ (rᶜ<Hᶜ xᶜ yᶜ) (m≤m+n Hᶜ z)

Hᶜ<Hᶜ+rⁱ : ∀ x y → Hᶜ < Hᶜ + rⁱ x y
Hᶜ<Hᶜ+rⁱ x y = begin
  1 + Hᶜ       ≡⟨ +-comm 1 Hᶜ ⟩
  Hᶜ + 1       ≤⟨ +-monoʳ-≤ Hᶜ (1≤rⁱ x y) ⟩
  Hᶜ + rⁱ x y ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of r

r-cong : r Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
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

x≈y⇒r≡0 : ∀ {X Y} → X ≈ Y → r X Y ≡ 0
x≈y⇒r≡0 {X} {Y} X≈Y with X ≟ Y
... | yes _   = refl
... | no  X≉Y = contradiction X≈Y X≉Y

r≡0⇒x≈y : ∀ {X Y} → r X Y ≡ 0 → X ≈ Y
r≡0⇒x≈y {X} {Y} r≡0 with X ≟ Y
... | yes X≈Y = X≈Y
... | no  _   with 𝑪? X | 𝑪? Y
...   | yes Xᶜ | yes Yᶜ  = rᶜ≡0⇒x≈y Xᶜ Yᶜ r≡0
...   | no  Xⁱ | _      = contradiction r≡0 λ()
...   | yes Xᶜ | no  Yⁱ = contradiction r≡0 λ()

r-sym : ∀ X Y → r X Y ≡ r Y X
r-sym X Y with X ≟ Y | Y ≟ X
... | yes _   | yes _   = refl
... | yes X≈Y | no  Y≉X = contradiction (≈-sym X≈Y) Y≉X
... | no  X≉Y | yes Y≈X = contradiction (≈-sym Y≈X) X≉Y
... | no _    | no _    with 𝑪? X | 𝑪? Y
...   | yes Xᶜ | yes Yᶜ = rᶜ-sym Xᶜ Yᶜ
...   | no  _  | no  _  = cong (Hᶜ +_) (rⁱ-sym X Y)
...   | no  _  | yes _  = cong (Hᶜ +_) (rⁱ-sym X Y)
...   | yes _  | no  _  = cong (Hᶜ +_) (rⁱ-sym X Y)

r-maxTriIneq-lemma : ∀ X Y Z → Hᶜ + rⁱ X Z ≤ (Hᶜ + rⁱ X Y) ⊔ (Hᶜ + rⁱ Y Z)
r-maxTriIneq-lemma X Y Z = begin
  Hᶜ + rⁱ X Z                    ≤⟨ +-monoʳ-≤ Hᶜ (rⁱ-maxTriIneq X Y Z) ⟩
  Hᶜ + (rⁱ X Y ⊔ rⁱ Y Z)        ≡⟨ +-distribˡ-⊔ Hᶜ _ _ ⟩
  (Hᶜ + rⁱ X Y) ⊔ (Hᶜ + rⁱ Y Z) ∎
  where open ≤-Reasoning

r-maxTriIneq : MaxTriangleInequality r
r-maxTriIneq x y z with x ≟ z | x ≟ y | y ≟ z
r-maxTriIneq x y z | yes _   | _       | _       = z≤n
r-maxTriIneq x y z | no  x≉z | yes x≈y | yes y≈z = contradiction (≈-trans x≈y y≈z) x≉z
r-maxTriIneq x y z | no  _   | yes x≈y | no  _   with 𝑪? x | 𝑪? y | 𝑪? z
... | yes xᶜ | yes yᶜ | yes zᶜ = ≤-reflexive (rᶜ-cong xᶜ zᶜ yᶜ zᶜ x≈y ≈-refl)
... | yes xᶜ | no  yⁱ | _     = contradiction (𝑪-cong x≈y xᶜ) yⁱ
... | no  xⁱ | yes yᶜ | _     = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
... | yes _  | yes _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (rⁱ-cong x≈y ≈-refl))
... | no  _  | no  _  | yes _ = +-monoʳ-≤ Hᶜ (≤-reflexive (rⁱ-cong x≈y ≈-refl))
... | no  _  | no  _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (rⁱ-cong x≈y ≈-refl))
r-maxTriIneq x y z | no  _   | no  _   | yes y≈z with 𝑪? x | 𝑪? y | 𝑪? z
... | yes xᶜ | yes yᶜ | yes zᶜ = m≤n⇒m≤n⊔o 0 (≤-reflexive (rᶜ-cong xᶜ zᶜ xᶜ yᶜ ≈-refl (≈-sym y≈z)))
... | _      | yes yᶜ | no  zⁱ = contradiction (𝑪-cong y≈z yᶜ) zⁱ
... | _      | no  yⁱ | yes zᶜ = contradiction (𝑪-cong (≈-sym y≈z) zᶜ) yⁱ
... | no  _  | yes _  | yes _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (rⁱ-cong ≈-refl (≈-sym y≈z))))
... | yes _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (rⁱ-cong ≈-refl (≈-sym y≈z))))
... | no  _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (rⁱ-cong ≈-refl (≈-sym y≈z))))
r-maxTriIneq x y z | no  _   | no  _   | no  _   with 𝑪? x | 𝑪? y | 𝑪? z
... | yes xᶜ | yes yᶜ | yes zᶜ = rᶜ-maxTriIneq xᶜ yᶜ zᶜ
... | yes xᶜ | yes yᶜ | no  zⁱ = m≤o⇒m≤n⊔o (rᶜ xᶜ yᶜ) (+-monoʳ-≤ Hᶜ (xᶜyᶜzⁱ⇒rⁱxz≤rⁱyz xᶜ yᶜ zⁱ))
... | no  xⁱ | yes yᶜ | yes zᶜ = m≤n⇒m≤n⊔o (rᶜ yᶜ zᶜ) (+-monoʳ-≤ Hᶜ (xⁱyᶜzᶜ⇒rⁱxz≤rⁱxy xⁱ yᶜ zᶜ))
... | yes xᶜ | no  yⁱ | yes zᶜ = m≤n⇒m≤n⊔o (Hᶜ + rⁱ y z) (<⇒≤ (rᶜ<Hᶜ+x xᶜ zᶜ _))
... | yes _  | no  _  | no  _  = r-maxTriIneq-lemma x y z
... | no  _  | yes _  | no  _  = r-maxTriIneq-lemma x y z
... | no  _  | no  _  | yes _  = r-maxTriIneq-lemma x y z
... | no  _  | no  _  | no  _  = r-maxTriIneq-lemma x y z

r≤Hᶜ+Hⁱ : ∀ x y → r x y ≤ Hᶜ + Hⁱ
r≤Hᶜ+Hⁱ x y with x ≟ y
... | yes _ = z≤n
... | no  _ with 𝑪? x | 𝑪? y
...   | no  _  | no  _  = +-monoʳ-≤ Hᶜ (rⁱ≤Hⁱ x y)
...   | no  _  | yes _  = +-monoʳ-≤ Hᶜ (rⁱ≤Hⁱ x y)
...   | yes _  | no  _  = +-monoʳ-≤ Hᶜ (rⁱ≤Hⁱ x y)
...   | yes xᶜ | yes yᶜ = ≤-trans (<⇒≤ (rᶜ<Hᶜ xᶜ yᶜ)) (m≤m+n Hᶜ Hⁱ)

r-bounded : Bounded r
r-bounded = Hᶜ + Hⁱ , r≤Hᶜ+Hⁱ

r-isPreMetric : IsPreMetric _≈_ r
r-isPreMetric = record
  { isTotalOrder    = ≤-isTotalOrder
  ; 0#-minimum      = z≤n
  ; ≈-isEquivalence = ≈-isEquivalence
  ; cong            = r-cong
  ; eq⇒0            = x≈y⇒r≡0
  }

r-isQuasiSemiMetric : IsQuasiSemiMetric _≈_ r
r-isQuasiSemiMetric = record
  { isPreMetric = r-isPreMetric
  ; 0⇒eq        = r≡0⇒x≈y
  }

r-isSemiMetric : IsSemiMetric _≈_ r
r-isSemiMetric = record
  { isQuasiSemiMetric = r-isQuasiSemiMetric
  ; sym               = r-sym
  }

r-isUltraMetric : IsUltraMetric _≈_ r
r-isUltraMetric = record
  { isSemiMetric = r-isSemiMetric
  ; triangle     = r-maxTriIneq
  }

r-ultraMetric : UltraMetric a ℓ
r-ultraMetric = record
  { d             = r
  ; isUltraMetric = r-isUltraMetric
  }

H<r : ∀ {x y} → x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ < r x y
H<r {x} {y} x≉y xⁱ⊎yⁱ with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
... | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
... | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ
... | no  _  | _      | _       = Hᶜ<Hᶜ+rⁱ x y
... | yes _  | no  _  | _       = Hᶜ<Hᶜ+rⁱ x y

rᶜ<r : ∀ {w x y z} (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) → y ≉ z → 𝑰 y ⊎ 𝑰 z  → rᶜ wᶜ xᶜ < r y z
rᶜ<r wᶜ xᶜ y≉z yⁱ⊎zⁱ = <-transʳ (<⇒≤ (rᶜ<Hᶜ wᶜ xᶜ)) (H<r y≉z yⁱ⊎zⁱ)

rᶜ≤r : ∀ {x y} → x ≉ y → (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ ≤ r x y
rᶜ≤r {x} {y} x≉y xᶜ yᶜ with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _ with 𝑪? x | 𝑪? y
...   | no  xⁱ  | _      = contradiction xᶜ xⁱ
...   | yes _   | no  yⁱ = contradiction yᶜ yⁱ
...   | yes xᶜ' | yes yᶜ' = begin
  DV.h (toCRoute xᶜ) ⊔ DV.h (toCRoute yᶜ) ≡⟨ sym (DVP.r[x,y]≡hx⊔hy x≉y) ⟩
  DV.r (toCRoute xᶜ)  (toCRoute yᶜ)       ≡⟨ DVP.r-cong ≈-refl ≈-refl ⟩
  DV.r (toCRoute xᶜ') (toCRoute yᶜ')      ≤⟨ ≤-refl ⟩
  rᶜ _ _                                 ∎

rᶜ≡r : ∀ {x y p q} (pᶜ : 𝑪 p) (qᶜ : 𝑪 q) → x ≈ p → y ≈ q → x ≉ y → rᶜ pᶜ qᶜ ≡ r x y
rᶜ≡r {x} {y} {p} {q} pᶜ qᶜ x≈p y≈q x≉y with x ≟ y | 𝑪? x | 𝑪? y
... | yes x≈y | _      | _      = contradiction x≈y x≉y
... | _       | no  xⁱ | _      = contradiction (𝑪-cong (≈-sym x≈p) pᶜ) xⁱ
... | _       | _      | no  yⁱ = contradiction (𝑪-cong (≈-sym y≈q) qᶜ) yⁱ
... | no _    | yes xᶜ | yes yᶜ = rᶜ-cong pᶜ qᶜ xᶜ yᶜ (≈-sym x≈p) (≈-sym y≈q)

H+rⁱ≡r : ∀ {x y} {w z} → w ≈ x → z ≈ y → x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ + rⁱ w z ≡ r x y
H+rⁱ≡r {x} {y} w≈x z≈y x≉y xⁱ⊎yⁱ with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
...   | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
...   | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ
...   | no  _  | _      | _       = cong (Hᶜ +_) (rⁱ-cong w≈x z≈y)
...   | yes _  | no  _  | _       = cong (Hᶜ +_) (rⁱ-cong w≈x z≈y)

r-force-rⁱ : ∀ (X Y : RoutingMatrix) {i j} →
              (∀ u v → r (X u v) (Y u v) ≤ Hᶜ + rⁱ (X i j) (Y i j)) →
              (∀ {u v} → X u v ≉ Y u v → 𝑰 (X u v) ⊎ 𝑰 (Y u v) →
               rⁱ (X u v) (Y u v) ≤ rⁱ (X i j) (Y i j))
r-force-rⁱ X Y r≤Hᶜ+rⁱXₗYₗ {u} {v} Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ =
  +-cancelˡ-≤ Hᶜ (≤-trans (≤-reflexive (H+rⁱ≡r ≈-refl ≈-refl Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ)) (r≤Hᶜ+rⁱXₗYₗ u v))

------------------------------------------------------------------------
-- Properties of d

private module MaxLiftₜ = MaxLift ℝ𝕋ₛⁱ (λ _ → r)

d-isUltraMetric : IsUltraMetric _ d
d-isUltraMetric = MaxLiftₜ.isUltraMetric r-isUltraMetric

open IsUltraMetric d-isUltraMetric public
  using ()
  renaming
  ( cong              to d-cong
  ; sym               to d-sym
  ; eq⇒0              to x≈y⇒d≡0
  ; 0⇒eq              to d≡0⇒x≈y
  ; isQuasiSemiMetric to d-isQuasiSemiMetric
  )

d-bounded : Bounded d
d-bounded = MaxLiftₜ.bounded r-bounded

r≤d : ∀ x y i → r (x i) (y i) ≤ d x y
r≤d = MaxLiftₜ.dᵢ≤d

------------------------------------------------------------------------
-- Properties of dₜᶜ

module _ (p : Subset n) where

  private module Conditionₜ = Condition d (_∈? p)

  dᶜ-cong : ∀ i → (dᶜ p i) Preserves₂ _≈ₜ_ ⟶ _≈ₜ_ ⟶ _≡_
  dᶜ-cong = Conditionₜ.cong′ d-cong

  dᶜ-sym : ∀ i x y → dᶜ p i x y ≡ dᶜ p i y x
  dᶜ-sym = Conditionₜ.sym d-sym

------------------------------------------------------------------------
-- Properties of Dˢ

module _ (p : Subset n) where

  private module MaxLiftₘ = MaxLift ℝ𝕄ₛⁱ (dᶜ p)
  private module Conditionₜ = Condition d (_∈? p)
  Dₚ = D p

  D-sym : ∀ X Y → Dₚ X Y ≡ Dₚ Y X
  D-sym = MaxLiftₘ.sym (dᶜ-sym p _)

  D-cong : Dₚ Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
  D-cong = MaxLiftₘ.cong (dᶜ-cong p _)

  D≡0⇒X≈ₛY : ∀ {X Y} → Dₚ X Y ≡ 0 → X ≈ₘ[ p ] Y
  D≡0⇒X≈ₛY D≡0 i∈p = Conditionₜ.≡0⇒x≈y d≡0⇒x≈y i∈p (MaxLiftₘ.d≡0⇒dᵢ≡0 D≡0 _)

  d≤D : ∀ X Y i → (i ∈ p ⊎ X i ≈ₜ Y i) → d (X i) (Y i) ≤ Dₚ X Y
  d≤D X Y i cond  = subst (_≤ Dₚ X Y) (Conditionₜ.dᶜ≡d⁺ i (X i) (Y i) (map₂ x≈y⇒d≡0 cond)) (MaxLiftₘ.dᵢ≤d X Y i)

  r≤D : ∀ X Y i j → (i ∈ p ⊎ X i ≈ₜ Y i) → r (X i j) (Y i j) ≤ Dₚ X Y
  r≤D X Y i j op = ≤-trans (r≤d (X i) (Y i) j) (d≤D X Y i op)

  r≤D-wf : ∀ {X Y} → WellFormed p X → WellFormed p Y → ∀ i j → r (X i j) (Y i j) ≤ Dₚ X Y
  r≤D-wf {X} {Y} wfX wfY i j with i ∈? p
  ... | yes i∈p = r≤D X Y i j (inj₁ i∈p)
  ... | no  i∉p = r≤D X Y i j (inj₂ (WellFormed-cong wfX wfY i∉p))

  Y≉ₚX⇒0<DXY : ∀ {X Y} → Y ≉ₘ[ p ] X → 0 < Dₚ X Y
  Y≉ₚX⇒0<DXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₛ-sym ∘ D≡0⇒X≈ₛY)
