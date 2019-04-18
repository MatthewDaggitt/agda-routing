
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  where

open import Data.Fin using (Fin; toℕ) renaming (_≟_ to _≟𝔽_; _<_ to _<𝔽_)
open import Data.Fin.Properties using (toℕ≤pred[n])
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.List.Any using (index)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (module ≤-Reasoning; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Data.Product using (_×_; ∃; _,_; proj₂; map)
open import Function using (_∘_; id)
open import Relation.Binary using (_Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Fin.Properties using (toℕ-mono-<)
import RoutingLib.Data.List.Sorting.Properties as Sorting
open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
open import RoutingLib.Data.Nat.Properties
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift
open import RoutingLib.Function.Metric.Nat
open import RoutingLib.Data.List.Membership.Setoid.Properties using (index-cong)
open import RoutingLib.Function.Reasoning

import RoutingLib.Routing.Algebra.Properties.FiniteRoutingAlgebra as FiniteRoutingAlgebraProperties
import RoutingLib.Routing as Routing
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Metrics as Metrics

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open FiniteRoutingAlgebraProperties isRoutingAlgebra isFinite
open Metrics isRoutingAlgebra isFinite

open Sorting ≥₊-decTotalOrder using (index-mono-<)

private
  variable
    x y : Route
    
------------------------------------------------------------------------
-- Properties of h

h-cong : h Preserves _≈_ ⟶ _≡_
h-cong {x} {y} x≈y = begin⟨ x≈y ⟩
 ∴ x      ≈ y       $⟨ index-cong S (∈-routes x) (∈-routes y) routes! ⟩
 ∴ i[ x ] ≡ i[ y ]  $⟨ cong (suc ∘ toℕ) ⟩
 ∴ h x    ≡ h y     ∎

h-resp-< : h Preserves _<₊_ ⟶ _>_
h-resp-< {x} {y} x<y = begin⟨ x<y ⟩
 ∴ (x ≤₊ y) × (x ≉ y)   $⟨ map id (λ x≉y → x≉y ∘ ≈-sym) ⟩
 ∴ (x ≤₊ y) × (y ≉ x)   $⟨ index-mono-< routes↗ (∈-routes _) (∈-routes _) ⟩
 ∴ i[ y ] <𝔽 i[ x ]     $⟨ s≤s ∘ toℕ-mono-< ⟩
 ∴ h y < h x            ∎

h-resp-≤ : h Preserves _≤₊_ ⟶ _≥_
h-resp-≤ {x} {y} x≤y with x ≟ y
... | yes x≈y = ≤-reflexive (h-cong (≈-sym x≈y))
... | no  x≉y = <⇒≤ (h-resp-< (x≤y , x≉y))

1≤h : ∀ x → 1 ≤ h x
1≤h _ = s≤s z≤n

h≤H : ∀ x → h x ≤ H
h≤H x = subst (h x ≤_) (suc∘pred[n]≡n 1≤H) (s≤s (toℕ≤pred[n] (index (∈-routes x))))

------------------------------------------------------------------------
-- Properties of r

r-cong : r Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
r-cong {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
... | yes _   | yes _   = refl
... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
... | no  _   | no  _   = cong₂ _⊔_ (h-cong x≈y) (h-cong u≈v)

x≈y⇒r≡0 : x ≈ y → r x y ≡ 0
x≈y⇒r≡0 {x} {y} x≈y with x ≟ y
... | yes _   = refl
... | no  x≉y = contradiction x≈y x≉y

r≡0⇒x≈y : r x y ≡ 0 → x ≈ y
r≡0⇒x≈y {x} {y} r≡0 with x ≟ y
... | yes x≈y = x≈y
... | no  _   = contradiction (sym r≡0) (<⇒≢ (m≤n⇒m≤n⊔o (h y) (1≤h x)))

r≤H : ∀ x y → r x y ≤ H
r≤H x y with x ≟ y
... | yes _ = z≤n
... | no  _ = n≤m×o≤m⇒n⊔o≤m (h≤H x) (h≤H y)

r-bounded : Bounded r
r-bounded = H , r≤H

r-sym : ∀ x y → r x y ≡ r y x
r-sym x y with x ≟ y | y ≟ x
... | yes _   | yes _   = refl
... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y
... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x
... | no  _   | no  _   = ⊔-comm (h x) (h y)

r-maxTriIneq : MaxTriangleInequality r
r-maxTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
... | _       | _       | yes _  = z≤n
... | yes x≈y | yes y≈z | no x≉z = contradiction (≈-trans x≈y y≈z) x≉z
... | yes x≈y | no  _   | no _   = ≤-reflexive (cong (_⊔ h z) (h-cong x≈y))
... | no  _   | yes y≈z | no _   = ≤-reflexive (cong (h x ⊔_) (h-cong (≈-sym y≈z)))
... | no  _   | no  _   | no _   = ⊔-mono-≤ (m≤m⊔n (h x) (h y)) (n≤m⊔n (h y) (h z))

r[x,y]≡hx⊔hy : x ≉ y → r x y ≡ h x ⊔ h y
r[x,y]≡hx⊔hy {x} {y} x≉y with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _   = refl

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

------------------------------------------------------------------------
-- Properties of d

module _ {n : ℕ} where

  open Routing algebra n
  private module MaxLiftₜ = MaxLift ℝ𝕋ₛⁱ (λ _ → r)

  d-isUltraMetric : IsUltraMetric _≈ₜ_ d
  d-isUltraMetric = MaxLiftₜ.isUltraMetric r-isUltraMetric

  open IsUltraMetric d-isUltraMetric public
    using ()
    renaming
    ( cong              to d-cong
    ; sym               to d-sym
    ; 0⇒eq              to d≡0⇒x≈y
    ; eq⇒0              to x≈y⇒d≡0
    ; isQuasiSemiMetric to d-isQuasiSemiMetric
    )

  r≤d : ∀ x y i → r (x i) (y i) ≤ d x y
  r≤d = MaxLiftₜ.dᵢ≤d

  d-bounded : Bounded d
  d-bounded = MaxLiftₜ.bounded r-bounded

------------------------------------------------------------------------
-- Properties of dₜᶜ

module _ {n : ℕ} (p : Subset n) where

  open Routing algebra n
  private module Conditionₜ = Condition (d {n}) (_∈? p)

  dᶜ-cong : ∀ i → (dᶜ p i) Preserves₂ _≈ₜ_ ⟶ _≈ₜ_ ⟶ _≡_
  dᶜ-cong = Conditionₜ.cong′ d-cong

  dᶜ-sym : ∀ i x y → dᶜ p i x y ≡ dᶜ p i y x
  dᶜ-sym = Conditionₜ.sym d-sym

------------------------------------------------------------------------
-- Properties of Dˢ

module _ {n : ℕ} (p : Subset n) where

  open Routing algebra n
  private
    module MaxLiftₘ = MaxLift ℝ𝕄ₛⁱ (dᶜ p)
    module Conditionₜ = Condition (d {n}) (_∈? p)
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
