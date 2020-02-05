--------------------------------------------------------------------------------
-- Agda routing library
--
-- Proof that the metrics associated with a strictly increasing finite routing
-- algebra are strictly contracting in the right ways so as to ensure that
-- F∥ is an asynchronously metrically contracting operator (AMCO).
--------------------------------------------------------------------------------

open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.InternalDefinitions

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_DistanceVector
  {a b ℓ} {algebra   : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A            : AdjacencyMatrix algebra n)
  (heightFunction   : HeightFunction algebra A)
  where

open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec.Functional
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Function.Metric.Nat
import RoutingLib.Function.Metric.Construct.Condition as Condition
open import RoutingLib.Relation.Nullary.Decidable using ([_,_])

import RoutingLib.Routing.VectorBased.Synchronous                            as CoreVectorBasedRouting
import RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties  as CoreVectorBasedRoutingProperties

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra

--------------------------------------------------------------------------------
-- Proof for an individual adjacency matrix

open HeightFunction heightFunction public
open CoreVectorBasedRouting algebra A
open CoreVectorBasedRoutingProperties isRoutingAlgebra A

r : Route → Route → ℕ
r x y with x ≟ y
... | yes _ = zero
... | no  _ = h x ⊔ h y

r-cong : r Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
r-cong {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
... | yes _   | yes _   = refl
... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
... | no  _   | no  _   = cong₂ _⊔_ (h-cong x≈y) (h-cong u≈v)

x≈y⇒r≡0 : ∀ {x y} → x ≈ y → r x y ≡ 0
x≈y⇒r≡0 {x} {y} x≈y with x ≟ y
... | yes _   = refl
... | no  x≉y = contradiction x≈y x≉y

r≡0⇒x≈y : ∀ {x y} → r x y ≡ 0 → x ≈ y
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
... | no  _   | yes y≈z | no _   = ≤-reflexive (trans (cong (h x ⊔_) (h-cong (≈-sym y≈z))) (sym (⊔-identityʳ _)))
... | no  _   | no  _   | no _   = ⊔-mono-≤ (m≤m⊔n (h x) (h y)) (n≤m⊔n (h y) (h z))

r[x,y]≡hx⊔hy : ∀ {x y} → x ≉ y → r x y ≡ h x ⊔ h y
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

h[FXᵢⱼ]⊔h[FYᵢⱼ]<v : ∀ X Y {i j v} → F X i j <₊ F Y i j →
                    (∀ k → r (X k j) (Y k j) ≤ v) →
                    h (F X i j) ⊔ h (F Y i j) < v
h[FXᵢⱼ]⊔h[FYᵢⱼ]<v X Y {i} {j} {v} FXᵢⱼ<FYᵢⱼ@(FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) d≤v with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
... | inj₂ FXᵢⱼ≈Iᵢⱼ = contradiction FXᵢⱼ≈Iᵢⱼ (FXᵢⱼ<FYᵢⱼ⇒FXᵢⱼ≉Iᵢⱼ X Y FXᵢⱼ<FYᵢⱼ)
... | inj₁ (k , FXᵢⱼ≈AᵢₖXₖⱼ) = begin-strict
  h (F X i j) ⊔ h (F Y i j) ≡⟨ m≤n⇒n⊔m≡n (h-resp-≤ FXᵢⱼ<FYᵢⱼ) ⟩
  h (F X i j)               <⟨ h-resp-↝ (Xₖⱼ≉∞ , i , k , ≈-sym FXᵢⱼ≈AᵢₖXₖⱼ) ⟩
  h (X k j)                 ≤⟨ m≤m⊔n (h (X k j)) (h (Y k j)) ⟩
  h (X k j) ⊔ h (Y k j)     ≡⟨ sym (r[x,y]≡hx⊔hy Xₖⱼ≉Yₖⱼ) ⟩
  r (X k j) (Y k j)         ≤⟨ d≤v k ⟩
  v                         ∎
  where    

  FYᵢⱼ≰AᵢₖXₖⱼ : F Y i j ≰₊ A i k ▷ X k j
  FYᵢⱼ≰AᵢₖXₖⱼ FYᵢⱼ≤AᵢₖXₖⱼ = FXᵢⱼ≉FYᵢⱼ (≤₊-antisym FXᵢⱼ≤FYᵢⱼ (begin 
    F Y i j       ≤⟨ FYᵢⱼ≤AᵢₖXₖⱼ ⟩
    A i k ▷ X k j ≈⟨ ≈-sym FXᵢⱼ≈AᵢₖXₖⱼ ⟩
    F X i j       ∎))
    where open POR ≤₊-poset

  Xₖⱼ≉∞ : X k j ≉ ∞#
  Xₖⱼ≉∞ Xₖⱼ≈∞ = FYᵢⱼ≰AᵢₖXₖⱼ (begin
    F Y i j       ≤⟨ ≤₊-maximum _ ⟩
    ∞#            ≈⟨ ≈-sym (▷-fixedPoint (A i k)) ⟩
    A i k ▷ ∞#    ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈∞) ⟩
    A i k ▷ X k j ∎)
    where open POR ≤₊-poset

  Xₖⱼ≉Yₖⱼ : X k j ≉ Y k j
  Xₖⱼ≉Yₖⱼ Xₖⱼ≈Yₖⱼ = FYᵢⱼ≰AᵢₖXₖⱼ (begin
    F Y i j       ≤⟨ FXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k ⟩
    A i k ▷ Y k j ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈Yₖⱼ) ⟩
    A i k ▷ X k j ∎)
    where open POR ≤₊-poset

  open ≤-Reasoning

r[FXᵢⱼ,FYᵢⱼ]<v : ∀ X Y i j → ∀ {v} → 0 < v →
                 (∀ k → r (X k j) (Y k j) ≤ v) →
                 r (F X i j) (F Y i j) < v
r[FXᵢⱼ,FYᵢⱼ]<v X Y i j {v} 0<v r≤v with F X i j ≟ F Y i j
... | yes FXᵢⱼ≈FYᵢⱼ = 0<v
... | no  FXᵢⱼ≉FYᵢⱼ with ≤₊-total (F X i j) (F Y i j)
...   | inj₁ FXᵢⱼ≤FYᵢⱼ = h[FXᵢⱼ]⊔h[FYᵢⱼ]<v X Y (FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) r≤v
...   | inj₂ FYᵢⱼ≤FXᵢⱼ = begin-strict
  h (F X i j) ⊔ h (F Y i j) ≡⟨ ⊔-comm (h (F X i j)) (h (F Y i j)) ⟩
  h (F Y i j) ⊔ h (F X i j) <⟨ h[FXᵢⱼ]⊔h[FYᵢⱼ]<v Y X (FYᵢⱼ≤FXᵢⱼ , FXᵢⱼ≉FYᵢⱼ ∘ ≈-sym) (λ k → subst (_≤ v) (r-sym (X k j) (Y k j)) (r≤v k)) ⟩
  v                         ∎
  where open ≤-Reasoning

r-strContrOrbits : ∀ {X v} → 0 < v →
                   (∀ k l → r (X k l) (F X k l) ≤ v) →
                   ∀ i j → r (F X i j) (F (F X) i j) < v
r-strContrOrbits {X} 0<v leq i j = r[FXᵢⱼ,FYᵢⱼ]<v X (F X) i j 0<v (λ k → leq k j)

r-strContrFP : ∀ {X*} → F X* ≈ₘ X* → ∀ {X v} → 0 < v →
               (∀ k l → r (X* k l) (X k l) ≤ v) →
               ∀ i j → r (X* i j) (F X i j) < v
r-strContrFP {X*} FX*≈X* {X} {v} 0<v leq i j = begin-strict
  r (X* i j) (F X i j)   ≡⟨ r-cong (≈-sym (FX*≈X* i j)) ≈-refl ⟩
  r (F X* i j) (F X i j) <⟨ r[FXᵢⱼ,FYᵢⱼ]<v X* X i j 0<v (λ k → leq k j) ⟩
  v                      ∎
  where open ≤-Reasoning

routeDistanceFunction : RouteDistanceFunction algebra A
routeDistanceFunction = record
  { r                   = r
  ; r-isQuasiSemiMetric = r-isQuasiSemiMetric
  ; r-bounded           = r-bounded
  ; r-strContrOrbits    = r-strContrOrbits
  ; r-strContrFP        = r-strContrFP
  }
