--------------------------------------------------------------------------------
-- Agda routing library
--
-- Proof that the metrics associated with a strictly increasing finite routing
-- algebra are strictly contracting in the right ways so as to ensure that
-- F∥ is an asynchronously metrically contracting operator (AMCO).
--------------------------------------------------------------------------------

open import Data.List using (tabulate)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec.Functional
open import Function using (_∘_)
open import Function.Metric.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_DistanceVector
  {a b ℓ} {algebra   : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A            : AdjacencyMatrix algebra n)
  (heightFunction   : HeightFunction algebra A)
  where

open import Data.List.Extrema ≤-totalOrder using (max; v≤max⁺)

open import RoutingLib.Data.Nat.Properties
import RoutingLib.Function.Metric.Construct.Condition as Condition
open import RoutingLib.Relation.Nullary.Decidable using ([_,_])

import RoutingLib.Routing.VectorBased.Synchronous                            as CoreVectorBasedRouting
import RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties  as CoreVectorBasedRoutingProperties

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.Basics.Assignment algebra n

open HeightFunction heightFunction
open CoreVectorBasedRouting algebra A
open CoreVectorBasedRoutingProperties isRoutingAlgebra A


--------------------------------------------------------------------------------
-- Proof for an individual adjacency matrix

module _ (i : Node) where

  r : PathWeight → PathWeight → ℕ
  r x y with x ≟ y
  ... | yes _ = 0
  ... | no  _ = 1 + (h (i , x) ⊔ h (i , y))
  
  r-cong : r Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
  r-cong {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
  ... | yes _   | yes _   = refl
  ... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
  ... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
  ... | no  _   | no  _   = cong suc (cong₂ _⊔_ (h-cong (refl , x≈y)) (h-cong (refl , u≈v)))

  x≈y⇒r≡0 : ∀ {x y} → x ≈ y → r x y ≡ 0
  x≈y⇒r≡0 {x} {y} x≈y with x ≟ y
  ... | yes _   = refl
  ... | no  x≉y = contradiction x≈y x≉y

  r≡0⇒x≈y : ∀ {x y} → r x y ≡ 0 → x ≈ y
  r≡0⇒x≈y {x} {y} r≡0 with x ≟ y
  ... | yes x≈y = x≈y
  ... | no  _   = contradiction r≡0 1+n≢0

  r≤1+H : ∀ x y → r x y ≤ suc H
  r≤1+H x y with x ≟ y
  ... | yes _ = z≤n
  ... | no  _ = s≤s (n≤m×o≤m⇒n⊔o≤m (h≤H (i , x)) (h≤H (i , y)))

  r-bounded : Bounded r
  r-bounded = suc H , r≤1+H

  r-sym : ∀ x y → r x y ≡ r y x
  r-sym x y with x ≟ y | y ≟ x
  ... | yes _   | yes _   = refl
  ... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y
  ... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x
  ... | no  _   | no  _   = cong suc (⊔-comm (h (i , x)) (h (i , y)))

  r-maxTriIneq : MaxTriangleInequality r
  r-maxTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
  ... | _       | _       | yes _  = z≤n
  ... | yes x≈y | yes y≈z | no x≉z = contradiction (≈-trans x≈y y≈z) x≉z
  ... | yes x≈y | no  _   | no _   = s≤s (≤-reflexive (cong (_⊔ h (i , z)) (h-cong (refl , x≈y))))
  ... | no  _   | yes y≈z | no _   = s≤s (≤-reflexive (cong (h (i , x) ⊔_) (h-cong (refl , ≈-sym y≈z))))
  ... | no  _   | no  _   | no _   = s≤s (⊔-mono-≤ (m≤m⊔n (h (i , x)) (h (i , y))) (m≤n⊔m (h (i , y)) (h (i , z))))

  r[x,y]≡1+hx⊔hy : ∀ {x y} → x ≉ y → r x y ≡ 1 + (h (i , x) ⊔ h (i , y))
  r[x,y]≡1+hx⊔hy {x} {y} x≉y with x ≟ y
  ... | yes x≈y = contradiction x≈y x≉y
  ... | no  _   = refl

  r-isProtoMetric : IsProtoMetric _≈_ r
  r-isProtoMetric = record
    { isPartialOrder  = ≤-isPartialOrder
    ; nonNegative     = z≤n
    ; ≈-isEquivalence = ≈-isEquivalence
    ; cong            = r-cong
    }

  r-isPreMetric : IsPreMetric _≈_ r
  r-isPreMetric = record
    { isProtoMetric = r-isProtoMetric
    ; ≈⇒0           = x≈y⇒r≡0
    }

  r-isQuasiSemiMetric : IsQuasiSemiMetric _≈_ r
  r-isQuasiSemiMetric = record
    { isPreMetric = r-isPreMetric
    ; 0⇒≈         = r≡0⇒x≈y
    }

h[FXᵢⱼ]⊔h[FYᵢⱼ]<v : ∀ X Y {i j v} → F X i j <₊ F Y i j →
                    (∀ k → r k (X k j) (Y k j) ≤ v) →
                    1 + (h (i , F X i j) ⊔ h (i , F Y i j)) < v
h[FXᵢⱼ]⊔h[FYᵢⱼ]<v X Y {i} {j} {v} FXᵢⱼ<FYᵢⱼ@(FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) d≤v with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
... | inj₂ FXᵢⱼ≈Iᵢⱼ = contradiction FXᵢⱼ≈Iᵢⱼ (FXᵢⱼ<FYᵢⱼ⇒FXᵢⱼ≉Iᵢⱼ X Y FXᵢⱼ<FYᵢⱼ)
... | inj₁ (k , FXᵢⱼ≈AᵢₖXₖⱼ) = begin-strict
  1 + (h (i , F X i j) ⊔ h (i , F Y i j)) ≡⟨ cong suc (m≥n⇒m⊔n≡m (<⇒≤ (h-resp-< FXᵢⱼ<ₐₚFYᵢⱼ))) ⟩
  1 + (h (i , F X i j))                   <⟨  s≤s (h-resp-↝ (≈-sym FXᵢⱼ≈AᵢₖXₖⱼ , Xₖⱼ≉∞)) ⟩
  1 + (h (k , X k j))                     ≤⟨  s≤s (m≤m⊔n (h (k , X k j)) (h (k , Y k j))) ⟩
  1 + (h (k , X k j) ⊔ h (k , Y k j))     ≡˘⟨ r[x,y]≡1+hx⊔hy k Xₖⱼ≉Yₖⱼ ⟩
  r k (X k j) (Y k j)                     ≤⟨  d≤v k ⟩
  v                                       ∎
  where
  FXᵢⱼ<ₐₚFYᵢⱼ : (i , F X i j) <ₐₚ (i , F Y i j)
  FXᵢⱼ<ₐₚFYᵢⱼ = (refl , FXᵢⱼ≤FYᵢⱼ) , λ {(refl , eq) → FXᵢⱼ≉FYᵢⱼ eq}
  
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
                 (∀ k → r k (X k j) (Y k j) ≤ v) →
                 r i (F X i j) (F Y i j) < v
r[FXᵢⱼ,FYᵢⱼ]<v X Y i j {v} 0<v r≤v with F X i j ≟ F Y i j
... | yes FXᵢⱼ≈FYᵢⱼ = 0<v
... | no  FXᵢⱼ≉FYᵢⱼ with ≤₊-total (F X i j) (F Y i j)
...   | inj₁ FXᵢⱼ≤FYᵢⱼ = h[FXᵢⱼ]⊔h[FYᵢⱼ]<v X Y (FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) r≤v
...   | inj₂ FYᵢⱼ≤FXᵢⱼ = begin-strict
  1 + (h (i , F X i j) ⊔ h (i , F Y i j)) ≡⟨ cong suc (⊔-comm (h (i , F X i j)) (h (i , F Y i j))) ⟩
  1 + (h (i , F Y i j) ⊔ h (i , F X i j)) <⟨ h[FXᵢⱼ]⊔h[FYᵢⱼ]<v Y X (FYᵢⱼ≤FXᵢⱼ , FXᵢⱼ≉FYᵢⱼ ∘ ≈-sym) (λ k → subst (_≤ v) (r-sym k (X k j) (Y k j)) (r≤v k)) ⟩
  v                                   ∎
  where open ≤-Reasoning

r-strContrOrbits : ∀ {X v} → 0 < v →
                   (∀ k l → r k (X k l) (F X k l) ≤ v) →
                   ∀ i j → r i (F X i j) (F (F X) i j) < v
r-strContrOrbits {X} 0<v leq i j = r[FXᵢⱼ,FYᵢⱼ]<v X (F X) i j 0<v (λ k → leq k j)

r-strContrFP : ∀ {X*} → F X* ≈ₘ X* → ∀ {X v} → 0 < v →
               (∀ k l → r k (X* k l) (X k l) ≤ v) →
               ∀ i j → r i (X* i j) (F X i j) < v
r-strContrFP {X*} FX*≈X* {X} {v} 0<v leq i j = begin-strict
  r i (X* i j) (F X i j)   ≡⟨ r-cong i (≈-sym (FX*≈X* i j)) ≈-refl ⟩
  r i (F X* i j) (F X i j) <⟨ r[FXᵢⱼ,FYᵢⱼ]<v X* X i j 0<v (λ k → leq k j) ⟩
  v                        ∎
  where open ≤-Reasoning

routeDistanceFunction : RouteDistanceFunction algebra A
routeDistanceFunction = record
  { r                   = r
  ; r-isQuasiSemiMetric = r-isQuasiSemiMetric
  ; r-bounded           = r-bounded
  ; r-strContrOrbits    = r-strContrOrbits
  ; r-strContrFP        = r-strContrFP
  }
