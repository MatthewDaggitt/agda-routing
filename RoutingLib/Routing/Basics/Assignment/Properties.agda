--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the basic definitions about the assignment of a route
-- to a node.
--------------------------------------------------------------------------------

open import Data.Fin.Base as Fin using (Fin)
open import Data.Fin.Properties as Fin using (any?)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃₂; proj₁; proj₂)
import Data.Product.Relation.Binary.Pointwise.NonDependent as DirectProduct
import Data.Product.Relation.Binary.Lex.NonStrict as LexProduct
open import Function.Base using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?; ¬-reflects)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary as U using (Pred; _∈_; ∁)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict

import RoutingLib.Relation.Binary.PropositionalEquality as ≡

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Basics.Assignment.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import RoutingLib.Routing.Basics.Assignment algebra n
open import RoutingLib.Routing.Basics.Network algebra n
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra

private
  variable
    A : AdjacencyMatrix

--------------------------------------------------------------------------------
-- Properties of _≤ₐₚ_

≤ₐₚ-poset : Poset a ℓ ℓ
≤ₐₚ-poset = DirectProduct.×-poset (≡.poset (Fin n)) ≤₊-poset

open Poset ≤ₐₚ-poset public
  using () renaming
  ( ≤-respˡ-≈       to ≤ₐₚ-respˡ-≈ₐ
  ; ≤-respʳ-≈       to ≤ₐₚ-respʳ-≈ₐ
  ; refl            to ≤ₐₚ-refl
  ; reflexive       to ≤ₐₚ-reflexive
  ; trans           to ≤ₐₚ-trans
  ; antisym         to ≤ₐₚ-antisym
  ; isPreorder      to ≤ₐₚ-isPreorder
  ; isPartialOrder  to ≤ₐₚ-isPartialOrder
  )

--------------------------------------------------------------------------------
-- Properties of _<ₐₚ_

<ₐₚ-isStrictPartialOrder : IsStrictPartialOrder _≈ₐ_ _<ₐₚ_
<ₐₚ-isStrictPartialOrder = NonStrictToStrict.<-isStrictPartialOrder _≈ₐ_ _≤ₐₚ_ ≤ₐₚ-isPartialOrder

<ₐₚ-strictPartialOrder : StrictPartialOrder a ℓ ℓ
<ₐₚ-strictPartialOrder = record
  { isStrictPartialOrder = <ₐₚ-isStrictPartialOrder
  }

open StrictPartialOrder <ₐₚ-strictPartialOrder public
  using ()
  renaming
  ( <-resp-≈  to <ₐₚ-resp-≈ₐ
  ; <-respʳ-≈ to <ₐₚ-respʳ-≈ₐ
  ; <-respˡ-≈ to <ₐₚ-respˡ-≈ₐ
  ; irrefl    to <ₐₚ-irrefl
  ; asym      to <ₐₚ-asym
  ; trans     to <ₐₚ-trans
  )

<ₐₚ-≤ₐₚ-trans : Trans _<ₐₚ_ _≤ₐₚ_ _<ₐₚ_
<ₐₚ-≤ₐₚ-trans = NonStrictToStrict.<-≤-trans _ _≤ₐₚ_ ≈ₐ-sym ≤ₐₚ-trans ≤ₐₚ-antisym ≤ₐₚ-respʳ-≈ₐ

--------------------------------------------------------------------------------
-- Properties of _≤ₐₜ_

≤ₐₜ-decTotalOrder : DecTotalOrder a ℓ ℓ
≤ₐₜ-decTotalOrder = LexProduct.×-decTotalOrder (Fin.≤-decTotalOrder n) ≤₊-decTotalOrder

open DecTotalOrder ≤ₐₜ-decTotalOrder public
  using () renaming
  ( ≤-respˡ-≈       to ≤ₐₜ-respˡ-≈ₐ
  ; ≤-respʳ-≈       to ≤ₐₜ-respʳ-≈ₐ
  ; refl            to ≤ₐₜ-refl
  ; reflexive       to ≤ₐₜ-reflexive
  ; trans           to ≤ₐₜ-trans
  ; antisym         to ≤ₐₜ-antisym
  ; total           to ≤ₐₜ-total
  ; isPreorder      to ≤ₐₜ-isPreorder
  ; totalOrder      to ≤ₐₜ-totalOrder
  ; isDecTotalOrder to ≤ₐₜ-isDecTotalOrder
  )
    
--------------------------------------------------------------------------------
-- Properties of _<ₐₜ_

<ₐₜ-isStrictTotalOrder : IsStrictTotalOrder _≈ₐ_ _<ₐₜ_
<ₐₜ-isStrictTotalOrder = NonStrictToStrict.<-isStrictTotalOrder₂ _≈ₐ_ _≤ₐₜ_ ≤ₐₜ-isDecTotalOrder

<ₐₜ-strictTotalOrder : StrictTotalOrder a ℓ ℓ
<ₐₜ-strictTotalOrder = record
  { isStrictTotalOrder = <ₐₜ-isStrictTotalOrder
  }

open StrictTotalOrder <ₐₜ-strictTotalOrder public
  using ()
  renaming
  ( <-resp-≈  to <ₐₜ-resp-≈ₐ
  ; irrefl    to <ₐₜ-irrefl
  ; compare   to <ₐₜ-cmp
  ; asym      to <ₐₜ-asym
  ; trans     to <ₐₜ-trans
  )

<ₐₜ-≤ₐₜ-trans : Trans _<ₐₜ_ _≤ₐₜ_ _<ₐₜ_
<ₐₜ-≤ₐₜ-trans = NonStrictToStrict.<-≤-trans _ _≤ₐₜ_ ≈ₐ-sym ≤ₐₜ-trans ≤ₐₜ-antisym ≤ₐₜ-respʳ-≈ₐ
≤ₐₜ-<ₐₜ-trans : Trans _≤ₐₜ_ _<ₐₜ_ _<ₐₜ_
≤ₐₜ-<ₐₜ-trans = NonStrictToStrict.≤-<-trans _ _≤ₐₜ_ ≤ₐₜ-trans ≤ₐₜ-antisym ≤ₐₜ-respˡ-≈ₐ

≮ₐₜ∧≯ₐₜ⇒≈ₐ : ∀ {x y} → ¬ (x <ₐₜ y) → ¬ (y <ₐₜ x) → x ≈ₐ y
≮ₐₜ∧≯ₐₜ⇒≈ₐ {x} {y} ¬x<y ¬y<x with <ₐₜ-cmp x y
... | tri< x<y _   _   = contradiction x<y ¬x<y
... | tri≈ _   x≈y _   = x≈y
... | tri> _   _   y<x = contradiction y<x ¬y<x

--------------------------------------------------------------------------------
-- Properties of _↝_

_↝[_]?_ : ∀ x A y → Dec (x ↝[ A ] y)
(j , x) ↝[ A ]? (i , y) = (A i j ▷ x ≟ y) ×-dec ¬? (x ≟ ∞#)

↝-respˡ-≈ₐ : _↝[ A ]_ Respectsˡ _≈ₐ_
↝-respˡ-≈ₐ (refl , x≈y) (Aᵢⱼx≈z , x≉∞) =
  ≈-trans (▷-cong _ (≈-sym x≈y)) Aᵢⱼx≈z ,
  x≉∞ ∘ ≈-trans x≈y
  
↝-respʳ-≈ₐ : _↝[ A ]_ Respectsʳ _≈ₐ_
↝-respʳ-≈ₐ (refl , x≈y) (Aᵢⱼz≈x , x≉∞) = ≈-trans Aᵢⱼz≈x x≈y , x≉∞

↝-resp-≈ₐ : _↝[ A ]_ Respects₂ _≈ₐ_
↝-resp-≈ₐ {A} = ↝-respʳ-≈ₐ {A} , ↝-respˡ-≈ₐ {A}

-- If the algebra is increasing then x extends y implies
-- x is preferred over y
incr∧↝⇒≤₊ : IsIncreasing algebra → ∀ A {x y} → x ↝[ A ] y → value x ≤₊ value y
incr∧↝⇒≤₊ incr A (Aᵢⱼx≈y , x≉∞) = ≤₊-respʳ-≈ Aᵢⱼx≈y (incr _ _)

-- If the algebra is strictly increasing then x extends y implies
-- x is strictly preferred over y
strIncr∧↝⇒<₊ : IsStrictlyIncreasing algebra → ∀ A {x y} → x ↝[ A ] y → value x <₊ value y
strIncr∧↝⇒<₊ strIncr A (Aᵢⱼx≈y , x≉∞) = <₊-respʳ-≈ Aᵢⱼx≈y (strIncr _ x≉∞)

--------------------------------------------------------------------------------
-- Properties of _⊴_

-- If x is extended by y then x threatens y
↝⇒⊴ : ∀ A → _↝[ A ]_ ⇒ _⊴[ A ]_
↝⇒⊴ A (Aᵢⱼy≈x , y≉∞) = ≤₊-reflexive Aᵢⱼy≈x , y≉∞

-- If x threatens y and y is preferred to z then x threatens z.
⊴∧≤ₐₚ⇒⊴ : ∀ A → Trans _⊴[ A ]_ _≤ₐₚ_ _⊴[ A ]_
⊴∧≤ₐₚ⇒⊴ A (Aᵢⱼy≤x , y≉∞) (refl , x≤z) = ≤₊-trans Aᵢⱼy≤x x≤z , y≉∞

-- If x extends y and y is preferred to z then x threatens z
↝∧≤ₐₚ⇒⊴ : ∀ A → Trans _↝[ A ]_ _≤ₐₚ_ _⊴[ A ]_
↝∧≤ₐₚ⇒⊴ A y↝x x≤z = ⊴∧≤ₐₚ⇒⊴ A (↝⇒⊴ A y↝x) x≤z

x⊴y⇒A▷x≤₊y : ∀ A {i j x y} → (i , x) ⊴[ A ] (j , y) → A j i ▷ x ≤₊ y
x⊴y⇒A▷x≤₊y A (x↝z , z≤y) = x↝z

-- If the algebra is increasing then x threatens y implies x <₊ y
incr∧⊴⇒≤₊ : IsIncreasing algebra → ∀ A {x} y → x ⊴[ A ] y → value x ≤₊ value y
incr∧⊴⇒≤₊ incr A _ (A▷y≤x , _) = ≤₊-trans (incr _ _) A▷y≤x

-- If the algebra is strictly increasing then x threatens y implies x <₊ y
strIncr∧⊴⇒<₊ : IsStrictlyIncreasing algebra → ∀ A {x y} → x ⊴[ A ] y → value x <₊ value y
strIncr∧⊴⇒<₊ strIncr A (A▷y≤x , y≉∞) = <-≤₊-trans (strIncr _ y≉∞) A▷y≤x

{-
-- If the algebra is finite then the "threatens" relation is decidable
⊴-dec : IsFinite algebra → Decidable _⊴_
⊴-dec finite x y = Finite.any? finite (λ z → (x ↝? z) ×-dec (z ≤₊? y))
  λ u≈v → Prod.map (↝-respʳ-≈ u≈v) (≤₊-respˡ-≈ u≈v)
-}
