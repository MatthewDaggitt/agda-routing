
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
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
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
...   | yes xᶜ' | yes yᶜ' = begin
  DV.h (toCRoute xᶜ) ⊔ DV.h (toCRoute yᶜ) ≡⟨ sym (DV.r[x,y]≡hx⊔hy x≉y) ⟩
  DV.r (toCRoute xᶜ)  (toCRoute yᶜ)       ≡⟨ DV.r-cong ≈-refl ≈-refl ⟩
  DV.r (toCRoute xᶜ') (toCRoute yᶜ')      ≤⟨ ≤-refl ⟩
  rᶜ _ _                                  ∎

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

open import RoutingLib.Routing.VectorBased.Synchronous algebra A
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Properties as PathVectorProperties

open PathVectorProperties isRoutingAlgebra isPathAlgebra A

rⁱ-strContrOrbits-FX : ∀ {X i j} → 𝑰 (F X i j) →
                        ∀ {v} → (∀ k l → r (X k l) (F X k l) ≤ v) →
                        Hᶜ + hⁱ (F X i j) < v
rⁱ-strContrOrbits-FX {X} {i} {j} FXᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X i j FXᵢⱼⁱ
... | (k , Xₖⱼ≉FXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|FXᵢⱼ|) = begin-strict
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
...   | (k , Xₖⱼ≉FXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|FXₖⱼ|) = begin-strict
  Hᶜ + hⁱ (F (F X) i j)             <⟨ +-monoʳ-< Hᶜ (hⁱ-mono Xₖⱼⁱ F²Xᵢⱼⁱ (<-trans |Xₖⱼ|<|FXₖⱼ| |FXₗⱼ|<|F²Xₗⱼ|)) ⟩
  Hᶜ + hⁱ (X k j)                   ≤⟨ +-monoʳ-≤ Hᶜ (m≤m⊔n _ _) ⟩
  Hᶜ + (hⁱ (X k j) ⊔ hⁱ (F X k j))  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl Xₖⱼ≉FXₖⱼ (inj₁ Xₖⱼⁱ) ⟩
  r (X k j) (F X k j)               ≤⟨ r≤v k j ⟩
  v                                 ∎

rⁱ-strContrOn𝑪 : ∀ {X Y i j} → 𝑪ₘ X → 𝑰 (F Y i j) →
                  ∀ {v} → (∀ k l → r (X k l) (Y k l) ≤ v) →
                  Hᶜ + rⁱ (F X i j) (F Y i j) < v
rⁱ-strContrOn𝑪 {X} {Y} {i} {j} Xᶜ FYᵢⱼⁱ {v} r≤v with FXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ Y i j FYᵢⱼⁱ
... | (k , FYᵢⱼ≈AᵢₖYₖⱼ , Yₖⱼⁱ) = begin-strict
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
{-
rᶜ-strContr-𝑪𝑪 : ∀ {X Y} → (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) →
                 ∀ {i j} (FXᵢⱼᶜ : 𝑪 (F X i j)) (FYᵢⱼᶜ : 𝑪 (F Y i j)) →
                 ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                 rᶜ FXᵢⱼᶜ FYᵢⱼᶜ < v
rᶜ-strContr-𝑪𝑪 {X} {Y} Xᶜ Yᶜ {i} {j} FXᵢⱼᶜ FYᵢⱼᶜ {v} 0<v r≤v = begin-strict
  rᶜ FXᵢⱼᶜ FYᵢⱼᶜ                           ≡⟨⟩
  DV.r (toCRoute FXᵢⱼᶜ) (toCRoute FYᵢⱼᶜ)   ≡⟨ DV.r-cong ≈-refl ≈-refl ⟩
  DV.r (cFX i j) (cFY i j)                 ≡⟨ DV.r-cong (F-toCMatrix-commute Xᶜ (F-pres-𝑪ₘ Xᶜ) i j) (F-toCMatrix-commute Yᶜ (F-pres-𝑪ₘ Yᶜ) i j) ⟩
  DV.r (Fᶜ cX i j) (Fᶜ cY i j)             <⟨ DV.r[FXᵢⱼ,FYᵢⱼ]<v Aᶜ cX cY i j 0<v d≤v ⟩
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
...   | (k , l , Xₖₗⁱ) = begin-strict
  rᶜ FXᵢⱼᶜ  FYᵢⱼᶜ          <⟨ rᶜ<Hᶜ+x FXᵢⱼᶜ FYᵢⱼᶜ _ ⟩
  Hᶜ + rⁱ (X k l) (Y k l)  ≡⟨ H+rⁱ≡r ≈-refl ≈-refl (𝑪𝑰⇒≉ (Yᶜ k l) Xₖₗⁱ ∘ ≈-sym) (inj₁ Xₖₗⁱ) ⟩
  r (X k l) (Y k l)        ≤⟨ r≤v k l ⟩
  v                        ∎
  where open ≤-Reasoning
rᶜ-strContr-𝑪𝑰 {X} {Y} (inj₂ (Xᶜ , Yⁱ)) FXᵢⱼᶜ FYᵢⱼᶜ {v} r≤v with 𝑰ₘ-witness Yⁱ
... | (k , l , Yₖₗⁱ) = begin-strict
  rᶜ FXᵢⱼᶜ  FYᵢⱼᶜ          <⟨ rᶜ<Hᶜ+x FXᵢⱼᶜ FYᵢⱼᶜ _ ⟩
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
...     | (k , Xₖₙ≉FXₖₙ , Xₖₙⁱ , _) = begin-strict
  rᶜ FXᵢⱼᶜ  F²Xᵢⱼᶜ          <⟨ rᶜ<Hᶜ+x FXᵢⱼᶜ F²Xᵢⱼᶜ _ ⟩
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
-}

------------------------------------------------------------------------
-- r is contracting in the right way

r-strContrOrbits : ∀ {X} →
                   ∀ {v} → 0 < v → (∀ k l → r (X k l) (F X k l) ≤ v) →
                   ∀ i j → r (F X i j) (F (F X) i j) < v
r-strContrOrbits {X} 0<v r≤v i j
  with F X i j ≟ F (F X) i j | 𝑪? (F X i j) | 𝑪? (F (F X) i j)
... | yes FXᵢⱼ≈F²Xᵢⱼ | _         | _          = 0<v
... | no  _          | yes FXᵢⱼᶜ | yes F²Xᵢⱼᶜ  = {!!} --rᶜ-strContrOrbits FXᵢⱼᶜ F²Xᵢⱼᶜ 0<v r≤v
... | no  _          | no  FXᵢⱼⁱ | _          = rⁱ-strContrOrbits (inj₁ FXᵢⱼⁱ) r≤v
... | no  _          | yes _     | no  F²Xᵢⱼⁱ = rⁱ-strContrOrbits (inj₂ F²Xᵢⱼⁱ) r≤v

r-strContrOn𝑪 : ∀ {X Y} → 𝑪ₘ X →
                 ∀ {v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                 ∀ i j → r (F X i j) (F Y i j) < v
r-strContrOn𝑪 {X} {Y} Xᶜ 0<v r≤v i j
  with F X i j ≟ F Y i j | 𝑪? (F X i j) | 𝑪? (F Y i j)
... | yes FXᵢⱼ≈FYᵢⱼ | _         | _         = 0<v
... | no  FXᵢⱼ≉FYᵢⱼ | yes FXᵢⱼᶜ | yes FYᵢⱼᶜ = {!!} --rᶜ-strContrOn𝑪 Xᶜ FXᵢⱼᶜ FYᵢⱼᶜ 0<v r≤v
... | no  FXᵢⱼ≉FYᵢⱼ | yes _     | no  FYᵢⱼⁱ = rⁱ-strContrOn𝑪 Xᶜ FYᵢⱼⁱ r≤v
... | no  FXᵢⱼ≉FYᵢⱼ | no  FXᵢⱼⁱ | _         = contradiction (F-pres-𝑪ₘ Xᶜ i j) FXᵢⱼⁱ

r-strContrOn𝑪 : ∀ {X*} → F X* ≈ₘ X* →
                 ∀ {X v} → 0 < v → (∀ k l → r (X k l) (Y k l) ≤ v) →
                 ∀ i j → r (F X i j) (F Y i j) < v
r-strContrOn𝑪 FX*≈X* = ?

------------------------------------------------------------------------
-- Route distance function
------------------------------------------------------------------------

routeDistanceFunction : RouteDistanceFunction
routeDistanceFunction = record
  { r                   = r
  ; r-isQuasiSemiMetric = r-isQuasiSemiMetric
  ; r-bounded           = r-bounded
  ; r-strContrOrbits    = r-strContrOrbits
  ; r-strContrFP        = {!!}
  }
