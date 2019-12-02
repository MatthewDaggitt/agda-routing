
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import Data.Nat hiding (_≟_)

module RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.RouteDistanceFunction
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  (1≤n : 1 ≤ n)
  where

open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Bool using (if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Function.Metric.Nat

open ≤-Reasoning

import RoutingLib.Routing.Algebra.Construct.Consistent as Consistent
import RoutingLib.Routing.Algebra.Properties.FiniteRoutingAlgebra as FiniteRoutingAlgebraProperties
open import RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra isRoutingAlgebra isPathAlgebra

open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.RouteDistanceFunction isRoutingAlgebra A
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.HeightFunction

open Routing algebra n
open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open Consistent isRoutingAlgebra isPathAlgebra A

postulate heightFunctionᶜ : HeightFunction algebraᶜ Aᶜ

import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.RouteDistanceFunction
  isRoutingAlgebraᶜ Aᶜ heightFunctionᶜ as DV

private
  variable
    w x y z : Route
    i j : Fin n

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Height of inconsistent routes
hⁱ : Route → ℕ
hⁱ x with 𝑪? x
... | yes _ = 1
... | no  _ = suc n ∸ size x

-- Distance between inconsistent routes
rⁱ : Route → Route → ℕ
rⁱ x y = hⁱ x ⊔ hⁱ y

-- Distance between consistent routes
rᶜ : ∀ {x y} → 𝑪 x → 𝑪 y → ℕ
rᶜ xᶜ yᶜ = DV.r (toCRoute xᶜ) (toCRoute yᶜ)

-- Distance between routes
r : Route → Route → ℕ
r x y with x ≟ y | 𝑪? x | 𝑪? y
... | yes _ | _      | _      = zero
... | no  _ | yes xᶜ | yes yᶜ = rᶜ xᶜ yᶜ
... | no  _ | _      | _      = suc DV.H + rⁱ x y

------------------------------------------------------------------------
-- Basic properties
------------------------------------------------------------------------

1<1+n∸∣x∣ : 1 < suc n ∸ size x
1<1+n∸∣x∣ {x} = begin
  2                    ≡⟨ sym (m+n∸n≡m 2 n) ⟩
  2 + n ∸ n            ≤⟨ ∸-monoʳ-≤ (suc (suc n)) (size<n 1≤n x) ⟩
  2 + n ∸ suc (size x) ≡⟨⟩
  1 + n ∸ size x       ∎

------------------------------------------------------------------------
-- Properties of hⁱ
------------------------------------------------------------------------

Hⁱ : ℕ
Hⁱ = suc n

hⁱ-cong : x ≈ y → hⁱ x ≡ hⁱ y
hⁱ-cong {x} {y} x≈y with 𝑪? x | 𝑪? y
... | yes _  | yes _  = refl
... | no  xⁱ | yes yᶜ = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
... | yes xᶜ | no  yⁱ = contradiction (𝑪-cong x≈y xᶜ) yⁱ
... | no  _  | no  _  = cong (suc n ∸_) (size-cong x≈y)

hⁱ-mono : 𝑰 x → 𝑰 y → size x < size y → hⁱ y < hⁱ x
hⁱ-mono {x} {y} xⁱ yⁱ |x|<|y| with 𝑪? x | 𝑪? y
... | yes xᶜ | _      = contradiction xᶜ xⁱ
... | no  _  | yes yᶜ = contradiction yᶜ yⁱ
... | no  _  | no  _  = ∸-monoʳ-< |x|<|y| (size≤n+1 _)

hⁱ-decr : 𝑰 (A i j ▷ x) → hⁱ (A i j ▷ x) < hⁱ x
hⁱ-decr Aᵢⱼxⁱ = hⁱ-mono (▷-forces-𝑰 Aᵢⱼxⁱ) Aᵢⱼxⁱ (≤-reflexive (sizeⁱ-incr Aᵢⱼxⁱ))

1≤hⁱ : ∀ x → 1 ≤ hⁱ x
1≤hⁱ x with 𝑪? x
... | yes _ = s≤s z≤n
... | no  _ = m<n⇒0<n∸m (s≤s (<⇒≤ (size<n 1≤n x)))

hⁱ≤Hⁱ : ∀ x → hⁱ x ≤ Hⁱ
hⁱ≤Hⁱ x with 𝑪? x
... | yes _ = s≤s z≤n
... | no  _ = m∸n≤m Hⁱ (size x)


h[yᶜ]≤h[x] : 𝑪 y → ∀ x → hⁱ y ≤ hⁱ x
h[yᶜ]≤h[x] {y} yᶜ x with 𝑪? y
... | no yⁱ  = contradiction yᶜ yⁱ
... | yes _  = 1≤hⁱ x

h[yᶜ]<h[xⁱ] : 𝑪 y → 𝑰 x → hⁱ y < hⁱ x
h[yᶜ]<h[xⁱ] {y} {x} yᶜ xⁱ with 𝑪? y | 𝑪? x
... | no yⁱ | _      = contradiction yᶜ yⁱ
... | _     | yes xᶜ = contradiction xᶜ xⁱ
... | yes _ | no  _  = 1<1+n∸∣x∣

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

rⁱxⁱyᶜ≡hⁱxⁱ : 𝑰 x → 𝑪 y → rⁱ x y ≡ hⁱ x
rⁱxⁱyᶜ≡hⁱxⁱ {x} {y} xⁱ yᶜ with x ≟ y
... | yes x≈y = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
... | no  _   with 𝑪? x | 𝑪? y
...   | yes xᶜ | _      = contradiction xᶜ xⁱ
...   | no  _  | no yⁱ = contradiction yᶜ yⁱ
...   | no  _  | yes _ = m≤n⇒n⊔m≡n (<⇒≤ 1<1+n∸∣x∣)

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
Hᶜ = suc DV.H

rᶜ-cong : (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
           w ≈ y → x ≈ z → rᶜ wᶜ xᶜ ≡ rᶜ yᶜ zᶜ
rᶜ-cong wᶜ xᶜ yᶜ zᶜ w≈y x≈z = DV.r-cong
  {x = toCRoute wᶜ} {y = toCRoute yᶜ}
  {u = toCRoute xᶜ} {v = toCRoute zᶜ} w≈y x≈z

rᶜ-sym : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ ≡ rᶜ yᶜ xᶜ
rᶜ-sym xᶜ yᶜ = DV.r-sym (toCRoute xᶜ) (toCRoute yᶜ)

x≈y⇒rᶜ≡0 : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → x ≈ y → rᶜ xᶜ yᶜ ≡ 0
x≈y⇒rᶜ≡0 xᶜ yᶜ x≈y = DV.x≈y⇒r≡0 {toCRoute xᶜ} {toCRoute yᶜ} x≈y

rᶜ≡0⇒x≈y : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ ≡ 0 → x ≈ y
rᶜ≡0⇒x≈y xᶜ yᶜ d≡0 = DV.r≡0⇒x≈y {toCRoute xᶜ} {toCRoute yᶜ} d≡0

rᶜ-maxTriIneq : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
                rᶜ xᶜ zᶜ ≤ rᶜ xᶜ yᶜ ⊔ rᶜ yᶜ zᶜ
rᶜ-maxTriIneq xᶜ yᶜ zᶜ = DV.r-maxTriIneq (toCRoute xᶜ) (toCRoute yᶜ) (toCRoute zᶜ)

rᶜ<Hᶜ : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ < Hᶜ
rᶜ<Hᶜ xᶜ yᶜ = s≤s (DV.r≤H (toCRoute xᶜ) (toCRoute yᶜ))

rᶜ<Hᶜ+x : ∀ (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) z → rᶜ xᶜ yᶜ < Hᶜ + z
rᶜ<Hᶜ+x xᶜ yᶜ z = <-transˡ (rᶜ<Hᶜ xᶜ yᶜ) (m≤m+n Hᶜ z)

Hᶜ<Hᶜ+rⁱ : ∀ x y → Hᶜ < Hᶜ + rⁱ x y
Hᶜ<Hᶜ+rⁱ x y = begin
  1 + Hᶜ       ≡⟨ +-comm 1 Hᶜ ⟩
  Hᶜ + 1       ≤⟨ +-monoʳ-≤ Hᶜ (1≤rⁱ x y) ⟩
  Hᶜ + rⁱ x y ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of r
------------------------------------------------------------------------

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
  Hᶜ + rⁱ X Z                   ≤⟨ +-monoʳ-≤ Hᶜ (rⁱ-maxTriIneq X Y Z) ⟩
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

r-isProtoMetric : IsProtoMetric _≈_ r
r-isProtoMetric = record
  { isTotalOrder    = ≤-isTotalOrder
  ; 0#-minimum      = z≤n
  ; ≈-isEquivalence = ≈-isEquivalence
  ; cong            = r-cong
  }

r-isPreMetric : IsPreMetric _≈_ r
r-isPreMetric = record
  { isProtoMetric = r-isProtoMetric
  ; eq⇒0          = x≈y⇒r≡0
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

H<r : x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ < r x y
H<r {x} {y} x≉y xⁱ⊎yⁱ with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
... | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
... | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ
... | no  _  | _      | _       = Hᶜ<Hᶜ+rⁱ x y
... | yes _  | no  _  | _       = Hᶜ<Hᶜ+rⁱ x y

rᶜ<r : ∀ (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) → y ≉ z → 𝑰 y ⊎ 𝑰 z  → rᶜ wᶜ xᶜ < r y z
rᶜ<r wᶜ xᶜ y≉z yⁱ⊎zⁱ = <-transʳ (<⇒≤ (rᶜ<Hᶜ wᶜ xᶜ)) (H<r y≉z yⁱ⊎zⁱ)

rᶜ≤r : x ≉ y → (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → rᶜ xᶜ yᶜ ≤ r x y
rᶜ≤r {x} {y} x≉y xᶜ yᶜ with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _ with 𝑪? x | 𝑪? y
...   | no  xⁱ  | _      = contradiction xᶜ xⁱ
...   | yes _   | no  yⁱ = contradiction yᶜ yⁱ
...   | yes xᶜ' | yes yᶜ' = {!!}
{-
begin
  DV.h (toCRoute xᶜ) ⊔ DV.h (toCRoute yᶜ) ≡⟨ sym (DVP.r[x,y]≡hx⊔hy x≉y) ⟩
  DV.r (toCRoute xᶜ)  (toCRoute yᶜ)       ≡⟨ DVP.r-cong ≈-refl ≈-refl ⟩
  DV.r (toCRoute xᶜ') (toCRoute yᶜ')      ≤⟨ ≤-refl ⟩
  rᶜ _ _                                 ∎
-}

rᶜ≡r : ∀ {p q} (pᶜ : 𝑪 p) (qᶜ : 𝑪 q) → x ≈ p → y ≈ q → x ≉ y → rᶜ pᶜ qᶜ ≡ r x y
rᶜ≡r {x} {y} {p} {q} pᶜ qᶜ x≈p y≈q x≉y with x ≟ y | 𝑪? x | 𝑪? y
... | yes x≈y | _      | _      = contradiction x≈y x≉y
... | _       | no  xⁱ | _      = contradiction (𝑪-cong (≈-sym x≈p) pᶜ) xⁱ
... | _       | _      | no  yⁱ = contradiction (𝑪-cong (≈-sym y≈q) qᶜ) yⁱ
... | no _    | yes xᶜ | yes yᶜ = rᶜ-cong pᶜ qᶜ xᶜ yᶜ (≈-sym x≈p) (≈-sym y≈q)

H+rⁱ≡r : w ≈ x → z ≈ y → x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ + rⁱ w z ≡ r x y
H+rⁱ≡r {w} {x} {z} {y} w≈x z≈y x≉y xⁱ⊎yⁱ with x ≟ y
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
-- r is strictly contracting
------------------------------------------------------------------------



------------------------------------------------------------------------
-- Route distance function
------------------------------------------------------------------------

routeDistanceFunction : RouteDistanceFunction
routeDistanceFunction = record
  { r                   = r
  ; r-isQuasiSemiMetric = r-isQuasiSemiMetric
  ; r-bounded           = r-bounded
  ; r-strContrOrbits    = {!!}
  ; r-strContrFP        = {!!}
  }
