open import Data.Product using (∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; map; swap)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _⊔_; _+_; _∸_)
open import Data.Nat.Properties hiding (module ≤-Reasoning; _≟_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; ⁅_⁆; ∣_∣; ⊤)
open import Data.Fin.Subset.Properties using (x∈p∩q⁺; x∈⁅x⁆; ∈⊤)
open import Data.Fin.Dec using (_∈?_)
open import Data.Product using (∃₂; proj₂)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wellFounded)

open import RoutingLib.Data.Fin.Subset using (_\\_)
open import RoutingLib.Data.Fin.Subset.Properties using (∣p\\q∣<∣p∣; i∉p\\q⇒i∉p; i∉⁅j⁆)
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Data.Table.Properties using (max[t]<x; x<max[t])
open import RoutingLib.Function.Metric
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Consistency as Consistency
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Properties as PathAlgebraProperties
open import RoutingLib.Routing.Model as Model using (AdjacencyMatrix)
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Metrics as PathVectorMetrics
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Properties as PathVectorProperties
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Metrics as DistanceVectorMetrics
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Properties as DistanceVectorProperties

open ≤-Reasoning
  
module RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Properties
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  (1≤n : 1 ≤ n)
  where

open Model algebra n
open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open Consistency algebra isPathAlgebra A
open PathAlgebraProperties isPathAlgebra
open PathVectorProperties algebra isPathAlgebra A

open PathVectorMetrics isPathAlgebra A

private module DVP = DistanceVectorProperties isRoutingAlgebraᶜ isFiniteᶜ
-- private module DV = DistanceVectorMetrics isRoutingAlgebraᶜ isFiniteᶜ

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

postulate hⁱ-mono : ∀ {x y} → 𝑰 x → 𝑰 y → size x < size y → hⁱ y < hⁱ x
-- hⁱ-mono = ?

hⁱ-decr : ∀ {i j x} → 𝑰 (A i j ▷ x) → hⁱ (A i j ▷ x) < hⁱ x
hⁱ-decr {i} {j} {x} Aᵢⱼxⁱ with 𝑪? x | 𝑪? (A i j ▷ x)
... | yes xᶜ | _        = contradiction xᶜ (▷-forces-𝑰 Aᵢⱼxⁱ)
... | no  _  | yes Aᵢⱼxᶜ = contradiction Aᵢⱼxᶜ Aᵢⱼxⁱ
... | no  _  | no  _    = ∸-monoʳ-< (≤-reflexive (sizeⁱ-incr Aᵢⱼxⁱ)) (size≤n+1 _)


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
-- Properties of dᵣⁱ

dᵣⁱ-cong : dᵣⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
dᵣⁱ-cong x≈y u≈v = cong₂ _⊔_ (hⁱ-cong x≈y) (hⁱ-cong u≈v)

dᵣⁱ-sym : ∀ x y → dᵣⁱ x y ≡ dᵣⁱ y x
dᵣⁱ-sym x y = ⊔-comm (hⁱ x) (hⁱ y)

dᵣⁱ≡0⇒x≈y : ∀ {x y} → dᵣⁱ x y ≡ 0 → x ≈ y
dᵣⁱ≡0⇒x≈y {x} {y} dᵣⁱ≡0 = contradiction dᵣⁱ≡0 (m<n⇒n≢0 (m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)))

dᵣⁱ-maxTriIneq : MaxTriangleIneq S dᵣⁱ
dᵣⁱ-maxTriIneq x y z = begin
  hⁱ x ⊔ hⁱ z                   ≤⟨ ⊔-monoˡ-≤ (hⁱ z) (m≤m⊔n (hⁱ x) (hⁱ y)) ⟩
  hⁱ x ⊔ hⁱ y ⊔ hⁱ z            ≡⟨ ⊔-triangulate (hⁱ x) (hⁱ y) (hⁱ z) ⟩
  (hⁱ x ⊔ hⁱ y) ⊔ (hⁱ y ⊔ hⁱ z) ∎

1≤dᵣⁱ : ∀ x y → 1 ≤ dᵣⁱ x y
1≤dᵣⁱ x y = m≤n⇒m≤n⊔o (hⁱ y) (1≤hⁱ x)

dᵣⁱ≤Hⁱ : ∀ x y → dᵣⁱ x y ≤ Hⁱ
dᵣⁱ≤Hⁱ x y = n≤m×o≤m⇒n⊔o≤m (hⁱ≤Hⁱ x) (hⁱ≤Hⁱ y)

dᵣⁱ-bounded : Bounded S dᵣⁱ
dᵣⁱ-bounded = Hⁱ , dᵣⁱ≤Hⁱ

dᵣⁱxⁱyᶜ≡hⁱxⁱ : ∀ {x y} → 𝑰 x → 𝑪 y → dᵣⁱ x y ≡ hⁱ x
dᵣⁱxⁱyᶜ≡hⁱxⁱ {x} {y} xⁱ yᶜ with x ≟ y
... | yes x≈y = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
... | no  _   with 𝑪? x | 𝑪? y
...   | yes xᶜ | _      = contradiction xᶜ xⁱ
...   | no  _  | no yⁱ = contradiction yᶜ yⁱ
...   | no  _  | yes _ = m≤n⇒n⊔m≡n (<⇒≤ 1<1+n∸∣x∣)

postulate dᵣⁱxᶜyⁱ≡hⁱyⁱ : ∀ {x y} → 𝑪 x → 𝑰 y → dᵣⁱ x y ≡ hⁱ y

xⁱyᶜzᶜ⇒dᵣⁱxz≤dᵣⁱxy : ∀ {x y z} → 𝑰 x → 𝑪 y → 𝑪 z → dᵣⁱ x z ≤ dᵣⁱ x y
xⁱyᶜzᶜ⇒dᵣⁱxz≤dᵣⁱxy xⁱ yᶜ zᶜ =
  ≤-reflexive (trans (dᵣⁱxⁱyᶜ≡hⁱxⁱ xⁱ zᶜ) (sym (dᵣⁱxⁱyᶜ≡hⁱxⁱ xⁱ yᶜ)))

xᶜyᶜzⁱ⇒dᵣⁱxz≤dᵣⁱyz : ∀ {x y z} → 𝑪 x → 𝑪 y → 𝑰 z → dᵣⁱ x z ≤ dᵣⁱ y z
xᶜyᶜzⁱ⇒dᵣⁱxz≤dᵣⁱyz {x} {y} {z} xᶜ yᶜ zⁱ =
  subst₂ _≤_ (dᵣⁱ-sym z x) (dᵣⁱ-sym z y) (xⁱyᶜzᶜ⇒dᵣⁱxz≤dᵣⁱxy zⁱ yᶜ xᶜ)

------------------------------------------------------------------------
-- Properties of dᵣᶜ

dᵣᶜ-cong : ∀ {x y w z} (wᶜ : 𝑪 w) (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
           w ≈ y → x ≈ z → dᵣᶜ wᶜ xᶜ ≡ dᵣᶜ yᶜ zᶜ
dᵣᶜ-cong wᶜ xᶜ yᶜ zᶜ w≈y x≈z = DVP.d-cong
  {x = toCRoute wᶜ} {y = toCRoute yᶜ}
  {u = toCRoute xᶜ} {v = toCRoute zᶜ} w≈y x≈z

dᵣᶜ-sym : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ ≡ dᵣᶜ yᶜ xᶜ
dᵣᶜ-sym xᶜ yᶜ = DVP.d-sym (toCRoute xᶜ) (toCRoute yᶜ)

x≈y⇒dᵣᶜ≡0 : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → x ≈ y → dᵣᶜ xᶜ yᶜ ≡ 0
x≈y⇒dᵣᶜ≡0 xᶜ yᶜ x≈y = DVP.x≈y⇒d≡0 {toCRoute xᶜ} {toCRoute yᶜ} x≈y

dᵣᶜ≡0⇒x≈y : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ ≡ 0 → x ≈ y
dᵣᶜ≡0⇒x≈y xᶜ yᶜ d≡0 = DVP.d≡0⇒x≈y {toCRoute xᶜ} {toCRoute yᶜ} d≡0

dᵣᶜ-maxTriIneq : ∀ {x y z} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) (zᶜ : 𝑪 z) →
                dᵣᶜ xᶜ zᶜ ≤ dᵣᶜ xᶜ yᶜ ⊔ dᵣᶜ yᶜ zᶜ
dᵣᶜ-maxTriIneq xᶜ yᶜ zᶜ = DVP.d-maxTriIneq (toCRoute xᶜ) (toCRoute yᶜ) (toCRoute zᶜ)

{-
dᵣᶜ-bounded : ∃ λ n → ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ ≤ n
dᵣᶜ-bounded = _ , λ xᶜ yᶜ → dᶜ≤Hᶜ (toCRoute xᶜ) (toCRoute yᶜ)
-}
dᵣᶜ<Hᶜ : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → dᵣᶜ xᶜ yᶜ < Hᶜ
dᵣᶜ<Hᶜ xᶜ yᶜ = s≤s (DVP.d≤H (toCRoute xᶜ) (toCRoute yᶜ))

dᵣᶜ<Hᶜ+x : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) z → dᵣᶜ xᶜ yᶜ < Hᶜ + z
dᵣᶜ<Hᶜ+x xᶜ yᶜ z = <-transˡ (dᵣᶜ<Hᶜ xᶜ yᶜ) (m≤m+n Hᶜ z)

Hᶜ<Hᶜ+dᵣⁱ : ∀ x y → Hᶜ < Hᶜ + dᵣⁱ x y
Hᶜ<Hᶜ+dᵣⁱ x y = begin
  1 + Hᶜ       ≡⟨ +-comm 1 Hᶜ ⟩
  Hᶜ + 1       ≤⟨ +-monoʳ-≤ Hᶜ (1≤dᵣⁱ x y) ⟩
  Hᶜ + dᵣⁱ x y ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of dᵣ

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
...   | yes wᶜ | yes xᶜ  | yes yᶜ | yes zᶜ = dᵣᶜ-cong wᶜ yᶜ xᶜ zᶜ W≈X Y≈Z

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

dᵣ-maxTriIneq : MaxTriangleIneq S dᵣ
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
...   | no  _  | no  _  = +-monoʳ-≤ Hᶜ (dᵣⁱ≤Hⁱ x y)
...   | no  _  | yes _  = +-monoʳ-≤ Hᶜ (dᵣⁱ≤Hⁱ x y)
...   | yes _  | no  _  = +-monoʳ-≤ Hᶜ (dᵣⁱ≤Hⁱ x y)
...   | yes xᶜ | yes yᶜ = ≤-trans (<⇒≤ (dᵣᶜ<Hᶜ xᶜ yᶜ)) (m≤m+n Hᶜ Hⁱ)

dᵣ-bounded : Bounded S dᵣ
dᵣ-bounded = Hᶜ + Hⁱ , dᵣ≤Hᶜ+Hⁱ

dᵣ-isUltrametric : IsUltrametric S dᵣ
dᵣ-isUltrametric = record
  { cong        = dᵣ-cong
  ; eq⇒0        = x≈y⇒dᵣ≡0
  ; 0⇒eq        = dᵣ≡0⇒x≈y
  ; sym         = dᵣ-sym
  ; maxTriangle = dᵣ-maxTriIneq
  }

dᵣ-ultrametric : Ultrametric S
dᵣ-ultrametric = record
  { d             = dᵣ
  ; isUltrametric = dᵣ-isUltrametric
  }


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
... | no  _ with 𝑪? x | 𝑪? y
...   | no  xⁱ  | _      = contradiction xᶜ xⁱ
...   | yes _   | no  yⁱ = contradiction yᶜ yⁱ
...   | yes xᶜ' | yes yᶜ' = begin
  DV.h (toCRoute xᶜ) ⊔ DV.h (toCRoute yᶜ) ≡⟨ sym (DVP.dxy≡hx⊔hy x≉y) ⟩
  DV.d (toCRoute xᶜ)  (toCRoute yᶜ)       ≡⟨ DVP.d-cong ≈-refl ≈-refl ⟩
  DV.d (toCRoute xᶜ') (toCRoute yᶜ')      ≤⟨ ≤-refl ⟩
  dᵣᶜ _ _                                 ∎

dᵣᶜ≡dᵣ : ∀ {x y p q} (pᶜ : 𝑪 p) (qᶜ : 𝑪 q) → x ≈ p → y ≈ q → x ≉ y → dᵣᶜ pᶜ qᶜ ≡ dᵣ x y
dᵣᶜ≡dᵣ {x} {y} {p} {q} pᶜ qᶜ x≈p y≈q x≉y with x ≟ y | 𝑪? x | 𝑪? y
... | yes x≈y | _      | _      = contradiction x≈y x≉y
... | _       | no  xⁱ | _      = contradiction (𝑪-cong (≈-sym x≈p) pᶜ) xⁱ
... | _       | _      | no  yⁱ = contradiction (𝑪-cong (≈-sym y≈q) qᶜ) yⁱ
... | no _    | yes xᶜ | yes yᶜ = dᵣᶜ-cong pᶜ qᶜ xᶜ yᶜ (≈-sym x≈p) (≈-sym y≈q)

H+dᵣⁱ≡dᵣ : ∀ {x y} {w z} → w ≈ x → z ≈ y → x ≉ y → 𝑰 x ⊎ 𝑰 y → Hᶜ + dᵣⁱ w z ≡ dᵣ x y
H+dᵣⁱ≡dᵣ {x} {y} w≈x z≈y x≉y xⁱ⊎yⁱ with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _   with 𝑪? x | 𝑪? y | xⁱ⊎yⁱ
...   | yes xᶜ | yes yᶜ | inj₁ xⁱ = contradiction xᶜ xⁱ
...   | yes xᶜ | yes yᶜ | inj₂ yⁱ = contradiction yᶜ yⁱ
...   | no  _  | _      | _       = cong (Hᶜ +_) (dᵣⁱ-cong w≈x z≈y)
...   | yes _  | no  _  | _       = cong (Hᶜ +_) (dᵣⁱ-cong w≈x z≈y)

dᵣ-force-dᵣⁱ : ∀ (X Y : RoutingMatrix) {r s} →
              (∀ u v → dᵣ (X u v) (Y u v) ≤ Hᶜ + dᵣⁱ (X r s) (Y r s)) →
              (∀ {u v} → X u v ≉ Y u v → 𝑰 (X u v) ⊎ 𝑰 (Y u v) →
               dᵣⁱ (X u v) (Y u v) ≤ dᵣⁱ (X r s) (Y r s))
dᵣ-force-dᵣⁱ X Y {r} {s} dᵣ≤Hᶜ+dᵣⁱXₗYₗ {u} {v} Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ =
  +-cancelˡ-≤ Hᶜ (≤-trans (≤-reflexive (H+dᵣⁱ≡dᵣ ≈-refl ≈-refl Xᵤᵥ≉Yᵤᵥ Xᵤᵥⁱ⊎Yᵤᵥⁱ)) (dᵣ≤Hᶜ+dᵣⁱXₗYₗ u v))

------------------------------------------------------------------------
-- Properties of dₜ

private module MaxLiftₜ = MaxLift ℝ𝕋ₛⁱ (λ _ → dᵣ)

dₜ-isUltrametric : IsUltrametric _ dₜ
dₜ-isUltrametric = MaxLiftₜ.isUltrametric dᵣ-isUltrametric

open IsUltrametric dₜ-isUltrametric public
  using ()
  renaming
  ( cong to dₜ-cong
  ; sym  to dₜ-sym
  ; eq⇒0 to x≈y⇒dₜ≡0
  ; 0⇒eq to dₜ≡0⇒x≈y
  )

dₜ-bounded : Bounded ℝ𝕋ₛ dₜ
dₜ-bounded = MaxLiftₜ.bounded dᵣ-bounded

d≤dₜ : ∀ x y i → dᵣ (x i) (y i) ≤ dₜ x y
d≤dₜ = MaxLiftₜ.dᵢ≤d

------------------------------------------------------------------------
-- Properties of D

private module MaxLiftₘ = MaxLift ℝ𝕄ₛⁱ (λ _ → dₜ)

D-isUltrametric : IsUltrametric _ D
D-isUltrametric = MaxLiftₘ.isUltrametric dₜ-isUltrametric

D-bounded : Bounded ℝ𝕄ₛ D
D-bounded = MaxLiftₘ.bounded dₜ-bounded

open IsUltrametric D-isUltrametric public using ()
  renaming
  ( cong to D-cong
  ; 0⇒eq to D≡0⇒X≈Y
  ; eq⇒0 to X≈Y⇒D≡0
  ; sym to D-sym
  )

D<v : ∀ {X Y v} → 0 < v → (∀ i j → dᵣ (X i j) (Y i j) < v) → D X Y < v
D<v 0<v dXY<v = max[t]<x 0<v (λ i → max[t]<x 0<v (λ j → dXY<v i j))

v<D : ∀ {X Y v} → (∃₂ λ i j → v < dᵣ (X i j) (Y i j)) → v < D X Y
v<D (i , j , v<dXY) = x<max[t] 0 (inj₂ (i , x<max[t] 0 (inj₂ (j , v<dXY))))

Y≉X⇒0<DXY : ∀ {X Y} → Y ≉ₘ X → 0 < D X Y
Y≉X⇒0<DXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₘ-sym ∘ D≡0⇒X≈Y)

postulate dᵣ≤D : ∀ X Y i j → dᵣ (X i j) (Y i j) ≤ D X Y

postulate DXᶜYᶜ≡DᶜXY : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → D X Y ≡ DV.D (toCMatrix Xᶜ) (toCMatrix Yᶜ)
-- DXᶜYᶜ≡DᶜXY {X} {Y} Xᶜ Yᶜ = {!!}
