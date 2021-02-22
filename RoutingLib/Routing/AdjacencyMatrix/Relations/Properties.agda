open import RoutingLib.Routing
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.AdjacencyMatrix.Relations.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.AdjacencyMatrix.Relations algebra A

open import Data.Product using (∃₂; _,_)
open import Data.Fin.Base using (zero; suc; inject₁; toℕ)
open import Data.Fin.Properties using (any?; toℕ-inject₁)
open import Data.Fin.Patterns using (0F)
open import Data.Nat using (s≤s; _<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product as Prod using (_×_)
open import Function.Base using (flip; _∘_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive public using ([_]; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset

open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)
open import RoutingLib.Relation.Binary.Construct.Closure.Transitive
import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid.Properties as Finite

import Relation.Binary.Construct.NonStrictToStrict _≈_ _↝_ as NSTS

--------------------------------------------------------------------------------
-- Properties of _↝_

_↝?_ : Decidable _↝_
x ↝? y = ¬? (x ≟ ∞#) ×-dec (any? (λ i → any? (λ j → A i j ▷ x ≟ y)))

↝-respˡ-≈ : _↝_ Respectsˡ _≈_
↝-respˡ-≈ x≈y (x≉∞ , i , j , Aᵢⱼx≈z) = x≉∞ ∘ ≈-trans x≈y , i , j , ≈-trans (▷-cong (A i j) (≈-sym x≈y)) Aᵢⱼx≈z

↝-respʳ-≈ : _↝_ Respectsʳ _≈_
↝-respʳ-≈ x≈y (x≉∞ , i , j , Aᵢⱼz≈x) = x≉∞ , i , j , ≈-trans Aᵢⱼz≈x x≈y

↝-resp-≈ : _↝_ Respects₂ _≈_
↝-resp-≈ = ↝-respʳ-≈ , ↝-respˡ-≈

-- If the algebra is strictly increasing then x extends y implies
-- x is preferred over y
strIncr∧↝⇒<₊ : IsStrictlyIncreasing algebra → _↝_ ⇒ _<₊_
strIncr∧↝⇒<₊ strIncr (x≉∞ , i , j , Aᵢⱼx≈y) = <₊-respʳ-≈ Aᵢⱼx≈y (strIncr (A i j) x≉∞)

--------------------------------------------------------------------------------
-- Properties of _↝ₛ_

_↝ₛ?_ : Decidable _↝ₛ_
_↝ₛ?_ = NSTS.<-decidable _≟_ _↝?_

↝ₛ-respˡ-≈ : _↝ₛ_ Respectsˡ _≈_
↝ₛ-respˡ-≈ = NSTS.<-respˡ-≈ ≈-trans ↝-respˡ-≈

↝ₛ-respʳ-≈ : _↝ₛ_ Respectsʳ _≈_
↝ₛ-respʳ-≈ = NSTS.<-respʳ-≈ ≈-sym ≈-trans ↝-respʳ-≈

↝ₛ-resp-≈ : _↝ₛ_ Respects₂ _≈_
↝ₛ-resp-≈ = ↝ₛ-respʳ-≈ , ↝ₛ-respˡ-≈

--------------------------------------------------------------------------------
-- Properties of _↝*_

↝*-respˡ-≈ : _↝*_ Respectsˡ _≈_
↝*-respˡ-≈ = R⁺-respˡ-≈ ↝-respˡ-≈

↝*-respʳ-≈ : _↝*_ Respectsʳ _≈_
↝*-respʳ-≈ = R⁺-respʳ-≈ ↝-respʳ-≈

↝*-resp-≈ : _↝*_ Respects₂ _≈_
↝*-resp-≈ = R⁺-resp-≈ ↝-resp-≈

↝*-trans : Transitive _↝*_
↝*-trans [ x↝y ]      y↝*z = x↝y ∷ y↝*z
↝*-trans (x↝y ∷ x↝*y) y↝*z = x↝y ∷ ↝*-trans x↝*y y↝*z

--------------------------------------------------------------------------------
-- Properties of _⊴_

-- If x is extended by y then x threatens y
↝⇒⊴ : _↝_ ⇒ _⊴_
↝⇒⊴ {y = y} x↝y = y , x↝y , ≤₊-refl

-- If x threatens y and y is preferred to z then x threatens z.
⊴-≤₊-trans : Trans _⊴_ _≤₊_ _⊴_
⊴-≤₊-trans (i , j , Aᵢⱼx≤y) y≤z = i , j , ≤₊-trans Aᵢⱼx≤y y≤z

-- If the algebra is strictly increasing then x threatens y implies x <₊ y
strIncr∧⊴⇒<₊ : IsStrictlyIncreasing algebra → _⊴_ ⇒ _<₊_
strIncr∧⊴⇒<₊ strIncr (z , x↝z , z≤y) = <-≤₊-trans (strIncr∧↝⇒<₊ strIncr x↝z) z≤y

-- If the algebra is finite then the "threatens" relation is decidable
⊴-dec : IsFinite algebra → Decidable _⊴_
⊴-dec finite x y = Finite.any? finite (λ z → (x ↝? z) ×-dec (z ≤₊? y))
  λ u≈v → Prod.map (↝-respʳ-≈ u≈v) (≤₊-respˡ-≈ u≈v)
