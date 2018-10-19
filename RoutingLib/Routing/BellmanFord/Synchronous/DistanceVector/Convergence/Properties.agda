open import Data.Nat using (ℕ; suc; z≤n; s≤s; _≤_; _≥_; _<_; _⊔_)
open import Data.Nat.Properties hiding (module ≤-Reasoning)
open import Data.Fin using (Fin; toℕ) renaming (_<_ to _<𝔽_)
open import Data.Fin.Properties using (prop-toℕ-≤)
open import Data.List using (List; length)
open import Data.List.Any using (index)
open import Data.Product using (_,_; _×_; map)
open import Relation.Binary using (_Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; id; _$_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ℕ_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function.Reasoning

open import RoutingLib.Data.Fin.Properties using (toℕ-mono-<)
open import RoutingLib.Data.List.Membership.Setoid.Properties using (index-cong)
import RoutingLib.Data.List.Sorting.Properties as Sorting
open import RoutingLib.Data.Nat.Properties using (ℕₛ; suc∘pred[n]≡n)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; m≤n⇒m≤n⊔o; n≤m×o≤m⇒n⊔o≤m; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Function.Reasoning
open import RoutingLib.Function.Metric using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)
import RoutingLib.Function.Metric.MaxLift as MaxLift

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.FiniteProperties as FiniteProperties
import RoutingLib.Routing.Model as Model
open import RoutingLib.Routing.BellmanFord.ConvergenceConditions
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Metrics as Metrics

module RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  where

open Model algebra
open Metrics isRoutingAlgebra isFinite
open RawRoutingAlgebra algebra
open FiniteProperties isRoutingAlgebra isFinite hiding (H)

open Sorting ≥₊-decTotalOrder using (index-mono-<)

------------------------------------------------------------------------
-- Properties of h

h-cong : h Preserves _≈_ ⟶ _≡_
h-cong {u} {v} u≈v = begin⟨ u≈v ⟩
 ⇒ u      ≈ v       ∴⟨ index-cong S (∈-routes u) (∈-routes v) routes! ⟩
 ⇒ i[ u ] ≡ i[ v ]  ∴⟨ cong (suc ∘ toℕ) ⟩
 ⇒ h u    ≡ h v     ∎

h-resp-< : ∀ {u v} → u <₊ v → h v < h u
h-resp-< {u} {v} u<v = begin⟨ u<v ⟩
 ⇒ (u ≤₊ v) × (u ≉ v)   ∴⟨ map id (λ u≉v → u≉v ∘ ≈-sym) ⟩
 ⇒ (u ≤₊ v) × (v ≉ u)   ∴⟨ index-mono-< routes↗ (∈-routes _) (∈-routes _) ⟩
 ⇒ i[ v ] <𝔽 i[ u ]     ∴⟨ s≤s ∘ toℕ-mono-< ⟩
 ⇒ h v < h u            ∎

h-resp-≤ : h Preserves _≤₊_ ⟶ _≥_
h-resp-≤ {u} {v} u≤v with u ≟ v
... | yes u≈v = ≤-reflexive (h-cong (≈-sym u≈v))
... | no  u≉v = <⇒≤ (h-resp-< (u≤v , u≉v))
  
1≤h : ∀ x → 1 ≤ h x
1≤h _ = s≤s z≤n

h≤H : ∀ x → h x ≤ H
h≤H x = subst (h x ≤_) (suc∘pred[n]≡n 1≤H) (s≤s (prop-toℕ-≤ (index (∈-routes x))))

------------------------------------------------------------------------
-- Properties of d

d-cong : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
d-cong {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
... | yes _   | yes _   = refl
... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
... | no  _   | no  _   = cong₂ _⊔_ (h-cong x≈y) (h-cong u≈v)

x≈y⇒d≡0 : ∀ {x y} → x ≈ y → d x y ≡ 0
x≈y⇒d≡0 {x} {y} x≈y with x ≟ y
... | yes _   = refl
... | no  x≉y = contradiction x≈y x≉y

d≡0⇒x≈y : ∀ {x y} → d x y ≡ 0 → x ≈ y
d≡0⇒x≈y {x} {y} d≡0 with x ≟ y
... | yes x≈y = x≈y
... | no  _   = contradiction (sym d≡0) (<⇒≢ (m≤n⇒m≤n⊔o (h y) (1≤h x)))

d≤H : ∀ x y → d x y ≤ H
d≤H x y with x ≟ y
... | yes _ = z≤n
... | no  _ = n≤m×o≤m⇒n⊔o≤m (h≤H x) (h≤H y)

d-bounded : Bounded S d
d-bounded = H , d≤H

-- Unnecessary ?
d-sym : ∀ x y → d x y ≡ d y x
d-sym x y with x ≟ y | y ≟ x
... | yes _   | yes _   = refl
... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y
... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x
... | no  _   | no  _   = ⊔-comm (h x) (h y)

d-maxTriIneq : MaxTriangleIneq S d
d-maxTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
... | _       | _       | yes _  = z≤n
... | yes x≈y | yes y≈z | no x≉z = contradiction (≈-trans x≈y y≈z) x≉z
... | yes x≈y | no  _   | no _   = ≤-reflexive (cong₂ _⊔_ (h-cong x≈y) (refl {x = h z}))
... | no  _   | no  _   | no _   = ⊔-mono-≤ (m≤m⊔n (h x) (h y)) (n≤m⊔n (h y) (h z))
... | no  _   | yes y≈z | no _   = begin
  h x ⊔ h z     ≡⟨ cong (h x ⊔_) (h-cong (≈-sym y≈z)) ⟩
  h x ⊔ h y     ≡⟨ sym (⊔-identityʳ _) ⟩
  h x ⊔ h y ⊔ 0 ∎
  where open ≤-Reasoning

dxy≡hx⊔hy : ∀ {x y} → x ≉ y → d x y ≡ h x ⊔ h y
dxy≡hx⊔hy {x} {y} x≉y with x ≟ y
... | yes x≈y = contradiction x≈y x≉y
... | no  _   = refl

d-isUltrametric : IsUltrametric S d
d-isUltrametric = record
  { eq⇒0        = x≈y⇒d≡0
  ; 0⇒eq        = d≡0⇒x≈y
  ; sym         = d-sym
  ; maxTriangle = d-maxTriIneq
  ; cong        = d-cong
  }

d-ultrametric : Ultrametric S
d-ultrametric = record
  { d             = d
  ; isUltrametric = d-isUltrametric
  }

------------------------------------------------------------------------
-- Properties of dₜ

d≤dₜ : ∀ {n} x y i → d (x i) (y i) ≤ dₜ {n} x y
d≤dₜ = MaxLift.dᵢ≤d (ℝ𝕋ₛⁱ _) d

dₜ-bounded : ∀ n → Bounded (ℝ𝕋ₛ n) dₜ
dₜ-bounded n = MaxLift.bounded (ℝ𝕋ₛⁱ n) d-bounded

dₜ-isUltrametric : ∀ n → IsUltrametric _ (dₜ {n})
dₜ-isUltrametric n = MaxLift.isUltrametric _ d-isUltrametric

module _ {n : ℕ} where
  open IsUltrametric (dₜ-isUltrametric n) public
    using ()
    renaming
    ( cong to dₜ-cong
    ; sym  to dₜ-sym
    ; 0⇒eq to dₜ≡0⇒x≈y
    ; eq⇒0 to x≈y⇒dₜ≡0
    )

------------------------------------------------------------------------
-- Properties of D

dₜ≤D : ∀ {n} X Y i → dₜ (X i) (Y i) ≤ D {n} X Y
dₜ≤D = MaxLift.dᵢ≤d (ℝ𝕄ₛⁱ _) dₜ

d≤D : ∀ {n} X Y i j → d (X i j) (Y i j) ≤ D {n} X Y
d≤D X Y i j = ≤-trans (d≤dₜ (X i) (Y i) j) (dₜ≤D X Y i)

D-bounded : ∀ n → Bounded (ℝ𝕄ₛ n) D
D-bounded n = MaxLift.bounded (ℝ𝕄ₛⁱ n) (dₜ-bounded n)

D-isUltrametric : ∀ n → IsUltrametric _ (D {n})
D-isUltrametric n = MaxLift.isUltrametric _ (dₜ-isUltrametric n)

module _ {n : ℕ} where
  open IsUltrametric (D-isUltrametric n) public
    using ()
    renaming
    ( cong to D-cong
    ; sym  to D-sym
    ; 0⇒eq to D≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒D≡0
    )
