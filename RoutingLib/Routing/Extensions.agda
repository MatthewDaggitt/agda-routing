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
open import Function using (flip)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive using (Plus′)
open import Relation.Binary.Construct.Closure.Transitive public using ([_]; _∷_)

open import RoutingLib.Relation.Binary.Construct.TransitiveClosure
open import RoutingLib.Relation.Nullary using (Finite)

--------------------------------------------------------------------------------
-- Definitions

-- x can be directly extended to form y
_↝_ : Route → Route → Set ℓ
x ↝ y = ∃₂ λ i j → A i j ▷ x ≈ y 

_↜_ : Route → Route → Set ℓ
_↜_ = flip _↝_

-- x can be extended to form y
_↝*_ : Route → Route → Set _
_↝*_ = Plus′ _↝_


--------------------------------------------------------------------------------
-- Properties of _↝_

_↝?_ : Decidable _↝_
x ↝? y = any? (λ i → any? (λ j → A i j ▷ x ≟ y))

↝-respˡ-≈ : _↝_ Respectsˡ _≈_
↝-respˡ-≈ x≈y (i , j , Aᵢⱼx≈z) = i , j , ≈-trans (▷-cong (A i j) (≈-sym x≈y)) Aᵢⱼx≈z

↝-respʳ-≈ : _↝_ Respectsʳ _≈_
↝-respʳ-≈ x≈y (i , j , Aᵢⱼz≈x) = i , j , ≈-trans Aᵢⱼz≈x x≈y

↝-resp-≈ : _↝_ Respects₂ _≈_
↝-resp-≈ = ↝-respʳ-≈ , ↝-respˡ-≈

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

↝*-dec : Finite Route → Decidable _↝*_
↝*-dec finite = R⁺? finite _↝?_
