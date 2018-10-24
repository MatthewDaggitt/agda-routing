open import Data.Nat using (ℕ; suc; z≤n; s≤s; _≤_; _≥_; _<_; _⊔_)
open import Data.Nat.Properties hiding (module ≤-Reasoning; _≟_)
open import Data.Fin using (Fin; toℕ) renaming (_<_ to _<𝔽_)
open import Data.Fin.Properties using (toℕ≤pred[n])
open import Data.List using (List; length)
open import Data.List.Any using (index)
open import Data.Product using (∃₂; _,_; _×_; map)
open import Data.Sum using (inj₁; inj₂)
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
open import RoutingLib.Data.Table.Properties using (max[t]<x; x<max[t])
open import RoutingLib.Function.Reasoning
open import RoutingLib.Function.Metric using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift

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
h≤H x = subst (h x ≤_) (suc∘pred[n]≡n 1≤H) (s≤s (toℕ≤pred[n] (index (∈-routes x))))

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
... | yes x≈y | no  _   | no _   = ≤-reflexive (cong (_⊔ h z) (h-cong x≈y))
... | no  _   | yes y≈z | no _   = ≤-reflexive (cong (h x ⊔_) (h-cong (≈-sym y≈z)))
... | no  _   | no  _   | no _   = ⊔-mono-≤ (m≤m⊔n (h x) (h y)) (n≤m⊔n (h y) (h z))

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

module _ {n : ℕ} where

  open Model algebra n
  private module MaxLiftₜ = MaxLift ℝ𝕋ₛⁱ (λ _ → d)

  dₜ-isUltrametric : IsUltrametric _ dₜ
  dₜ-isUltrametric = MaxLiftₜ.isUltrametric d-isUltrametric

  open IsUltrametric dₜ-isUltrametric public
    using ()
    renaming
    ( cong to dₜ-cong
    ; sym  to dₜ-sym
    ; 0⇒eq to dₜ≡0⇒x≈y
    ; eq⇒0 to x≈y⇒dₜ≡0
    )

  d≤dₜ : ∀ x y i → d (x i) (y i) ≤ dₜ {n} x y
  d≤dₜ = MaxLiftₜ.dᵢ≤d

  dₜ-bounded : Bounded ℝ𝕋ₛ dₜ
  dₜ-bounded = MaxLiftₜ.bounded d-bounded

------------------------------------------------------------------------
-- Properties of D

module _ {n : ℕ} where

  open Model algebra n
  private module MaxLiftₘ = MaxLift ℝ𝕄ₛⁱ (λ _ → dₜ)

  D-isUltrametric : IsUltrametric _ (D {n})
  D-isUltrametric = MaxLiftₘ.isUltrametric dₜ-isUltrametric

  open IsUltrametric D-isUltrametric public
    using ()
    renaming
    ( cong to D-cong
    ; sym  to D-sym
    ; 0⇒eq to D≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒D≡0
    )

  dₜ≤D : ∀ X Y i → dₜ (X i) (Y i) ≤ D {n} X Y
  dₜ≤D = MaxLiftₘ.dᵢ≤d

  d≤D : ∀ X Y i j → d (X i j) (Y i j) ≤ D {n} X Y
  d≤D X Y i j = ≤-trans (d≤dₜ (X i) (Y i) j) (dₜ≤D X Y i)

  D-bounded : Bounded ℝ𝕄ₛ D
  D-bounded = MaxLiftₘ.bounded dₜ-bounded

  module _ {X Y : RoutingMatrix} where
  
    Y≉X⇒0<DXY : Y ≉ₘ X → 0 < D X Y
    Y≉X⇒0<DXY Y≉X = n≢0⇒0<n (Y≉X ∘ ≈ₘ-sym ∘ D≡0⇒X≈Y)

    D<v : ∀ {v} → 0 < v → (∀ i j → d (X i j) (Y i j) < v) → D X Y < v
    D<v 0<v dXY<v = max[t]<x 0<v (λ i → max[t]<x 0<v (λ j → dXY<v i j))

    v<D : ∀ {v} → (∃₂ λ i j → v < d (X i j) (Y i j)) → v < D X Y
    v<D (i , j , v<dXY) = x<max[t] 0 (inj₂ (i , x<max[t] 0 (inj₂ (j , v<dXY))))
