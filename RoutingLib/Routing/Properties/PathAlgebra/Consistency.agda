import Algebra.FunctionProperties as AlgebraicProperties
open import Data.Fin using (Fin)
open import Data.List using (List; map)
import Data.List.Membership.Setoid as Membership
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Function using (_on_)
open import Level using (_⊔_) renaming (zero to ℓ₀)
open import Relation.Binary
import Relation.Binary.On as On
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import Data.List.Membership.Setoid.Properties
open import RoutingLib.Data.SimplePath using (SimplePath)
open import RoutingLib.Data.SimplePath.Enumeration
open import RoutingLib.Data.SimplePath.Relation.Equality using (ℙₛ)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Properties.PathAlgebra
  as PathAlgebraProperties

module RoutingLib.Routing.Properties.PathAlgebra.Consistency
  {a b ℓ n} (algebra : PathAlgebra a b ℓ n)
  where

open PathAlgebra algebra
open PathAlgebraProperties algebra

------------------------------------------------------------------------------
-- Types

CRoute : Set _
CRoute = Σ Route 𝑪

CStep : Set _
CStep = Fin n × Fin n

------------------------------------------------------------------------------
-- Special routes

C0# : CRoute
C0# = 0# , 0ᶜ

C∞ : CRoute
C∞ = ∞ , ∞ᶜ

------------------------------------------------------------------------------
-- Equality

infix 4 _≈ᶜ_ _≉ᶜ_ _≟ᶜ_

_≈ᶜ_ : Rel CRoute _
_≈ᶜ_ = _≈_ on proj₁

_≉ᶜ_ : Rel CRoute _
r ≉ᶜ s = ¬ (r ≈ᶜ s)

_≟ᶜ_ : Decidable _≈ᶜ_
_ ≟ᶜ _ = _ ≟ _

≈ᶜ-isDecEquivalence : IsDecEquivalence _≈ᶜ_
≈ᶜ-isDecEquivalence = On.isDecEquivalence proj₁ ≈-isDecEquivalence

Sᶜ : Setoid _ _
Sᶜ = On.setoid {B = CRoute} S proj₁

DSᶜ : DecSetoid _ _
DSᶜ = On.decSetoid {B = CRoute} DS proj₁

------------------------------------------------------------------------------
-- Choice operator

open AlgebraicProperties _≈ᶜ_

infix 7 _⊕ᶜ_

_⊕ᶜ_ : Op₂ CRoute
(r , rᶜ) ⊕ᶜ (s , sᶜ) = r ⊕ s , ⊕-pres-𝑪 rᶜ sᶜ

⊕ᶜ-cong : Congruent₂ _⊕ᶜ_
⊕ᶜ-cong = ⊕-cong

⊕ᶜ-assoc : Associative _⊕ᶜ_
⊕ᶜ-assoc _ _ _ = ⊕-assoc _ _ _

⊕ᶜ-comm : Commutative _⊕ᶜ_
⊕ᶜ-comm _ _ = ⊕-comm _ _

⊕ᶜ-sel : Selective _⊕ᶜ_
⊕ᶜ-sel _ _ = ⊕-sel _ _

⊕ᶜ-zeroʳ : RightZero C0# _⊕ᶜ_
⊕ᶜ-zeroʳ _ = ⊕-zeroʳ _

⊕ᶜ-identityʳ : RightIdentity C∞ _⊕ᶜ_
⊕ᶜ-identityʳ _ = ⊕-identityʳ _

------------------------------------------------------------------------------
-- Extension functions

infix 6 _▷ᶜ_

_▷ᶜ_ : CStep → CRoute → CRoute
(i , j) ▷ᶜ (r , rᶜ) = A i j ▷ r , ▷-pres-𝑪 i j rᶜ

▷ᶜ-cong : ∀ e {r s} → r ≈ᶜ s → e ▷ᶜ r ≈ᶜ e ▷ᶜ s
▷ᶜ-cong (i , j) = ▷-cong (A i j)

▷ᶜ-zero : ∀ e → e ▷ᶜ C∞ ≈ᶜ C∞
▷ᶜ-zero (i , j) = ▷-zero (A i j)

------------------------------------------------------------------------------
-- Finiteness

open Membership Sᶜ using () renaming (_∈_ to _∈ₗ_)

pathToCRoute : SimplePath n → CRoute
pathToCRoute p = weight p , weightᶜ p

abstract

  allCRoutes : List CRoute
  allCRoutes = map pathToCRoute (allPaths n)

  ∈-allCRoutes : ∀ r → r ∈ₗ allCRoutes
  ∈-allCRoutes (r , rᶜ) = ∈-resp-≈ Sᶜ {x = pathToCRoute (path r)} {r , rᶜ}
    rᶜ (∈-map⁺ (ℙₛ n) Sᶜ weight-cong (∈-allPaths (path r))) 
    
------------------------------------------------------------------------------
-- Routing algebra

rawAlgebraᶜ : RawRoutingAlgebra _ _ _
rawAlgebraᶜ = record
  { Step  = CStep
  ; Route = CRoute
  ; _≈_   = _≈ᶜ_
  ; _⊕_   = _⊕ᶜ_
  ; _▷_   = _▷ᶜ_
  ; 0#    = C0#
  ; ∞     = C∞
  
  ; ≈-isDecEquivalence = ≈ᶜ-isDecEquivalence
  ; ⊕-cong             = λ {w} {x} {y} {z} → ⊕ᶜ-cong {w} {x} {y} {z}
  ; ▷-cong             = ▷ᶜ-cong
  }

isRoutingAlgebraᶜ : IsRoutingAlgebra rawAlgebraᶜ
isRoutingAlgebraᶜ = record
  { ⊕-sel              = ⊕ᶜ-sel
  ; ⊕-comm             = ⊕ᶜ-comm
  ; ⊕-assoc            = ⊕ᶜ-assoc
  ; ⊕-zeroʳ            = ⊕ᶜ-zeroʳ
  ; ⊕-identityʳ        = ⊕ᶜ-identityʳ
  ; ▷-zero             = ▷ᶜ-zero
  }

routingAlgebraᶜ : RoutingAlgebra ℓ₀ (b ⊔ ℓ) ℓ
routingAlgebraᶜ = record
  { isRoutingAlgebra = isRoutingAlgebraᶜ
  }

------------------------------------------------------------------------------
-- Conversion

toCRoute : ∀ {r} → 𝑪 r → CRoute
toCRoute {r} rᶜ = r , rᶜ

fromCRoute : CRoute → Route
fromCRoute (r , _ ) = r

------------------------------------------------------------------------------
-- Adjacency matrix

Ac : SquareMatrix (Fin n × Fin n) n
Ac i j = (i , j)
