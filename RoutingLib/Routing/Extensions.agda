open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Extensions
  {a b ℓ n}
  (alg : RawRoutingAlgebra a b ℓ)
  (A : AdjacencyMatrix alg n)
  where

open RawRoutingAlgebra alg

open import Data.Product using (∃₂; _,_)
open import Data.Fin.Properties using (any?)
open import Data.Product using (_×_)
open import Function using (flip)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive
  using () renaming (Plus′ to TransitiveClosure)
open import Relation.Binary.Construct.Closure.Transitive public using ([_]; _∷_)

open import RoutingLib.Relation.Binary.Construct.Closure.Transitive

--------------------------------------------------------------------------------
-- Definitions

-- x can be directly extended to form y
_↝_ : Route → Route → Set ℓ
x ↝ y = ∃₂ λ i j → A i j ▷ x ≈ y 

-- x can be strictly extended to form y
_↝ₛ_ : Route → Route → Set ℓ
x ↝ₛ y = x ↝ y × x ≉ y

-- x can be extended to form y
_↝*_ : Route → Route → Set _
_↝*_ = TransitiveClosure _↝_

--------------------------------------------------------------------------------
-- Properties of _↝_

import Relation.Binary.Construct.NonStrictToStrict _≈_ _↝_ as NSTS

_↝?_ : Decidable _↝_
x ↝? y = any? (λ i → any? (λ j → A i j ▷ x ≟ y))

↝-respˡ-≈ : _↝_ Respectsˡ _≈_
↝-respˡ-≈ x≈y (i , j , Aᵢⱼx≈z) = i , j , ≈-trans (▷-cong (A i j) (≈-sym x≈y)) Aᵢⱼx≈z

↝-respʳ-≈ : _↝_ Respectsʳ _≈_
↝-respʳ-≈ x≈y (i , j , Aᵢⱼz≈x) = i , j , ≈-trans Aᵢⱼz≈x x≈y

↝-resp-≈ : _↝_ Respects₂ _≈_
↝-resp-≈ = ↝-respʳ-≈ , ↝-respˡ-≈

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
