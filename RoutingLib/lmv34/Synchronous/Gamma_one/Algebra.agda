open import Algebra.Core
open import Data.Bool.Base using (true; false; not)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _<_)
open import Data.Fin.Properties as Finₚ using (_≤?_; <-cmp) renaming (_≟_ to _≟F_)
open import Data.List using ([]; _∷_; List; foldr; filter; map; tabulate)
import Data.List.Sort as Sort
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Data.Product.Relation.Binary.Lex.NonStrict using (×-decTotalOrder)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-decSetoid)
open import Data.Vec.Functional using (Vector)
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties using () renaming (decSetoid to decSetoidᵥ)
open import Function using (_∘_)
open import Level using (_⊔_; 0ℓ; lift) renaming (suc to lsuc)
open import Relation.Binary as B using (Rel; DecTotalOrder; Setoid; DecSetoid; StrictTotalOrder; IsStrictTotalOrder)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Binary using (Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Construct.NonStrictToStrict using (<-isStrictTotalOrder₂) renaming (_<_ to _<ₗₑₓ_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no; ¬_; does; proof)
open import Relation.Nullary.Negation using (¬?; ¬-reflects)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Data.Product as Prod using (_×_; _,_)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.Routing as Routing
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebra

open import RoutingLib.Data.List using (partialMerge)
import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties

module RoutingLib.lmv34.Synchronous.Gamma_one.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open Routing algebra n using (RoutingMatrix; AdjacencyMatrix)
open RawRoutingAlgebra algebra
open RoutingAlgebra isRoutingAlgebra using (≤₊-decTotalOrder)

--------------------------------------------------------------------------------
-- Routing sets

RoutingSet : Set a
RoutingSet = List (Fin n × Route)

Ø : RoutingSet
Ø = []

-- RoutingVector setoid
FinRoute-decSetoid = ×-decSetoid (Finₚ.≡-decSetoid n) DS
open DecSetoid FinRoute-decSetoid public
  using () renaming
  ( _≈_           to _≈ᵣ_
  ; _≉_           to _≉ᵣ_
  ; refl          to ≈ᵣ-refl
  ; trans         to ≈ᵣ-trans
  ; sym           to ≈ᵣ-sym
  ; _≟_           to _≟ᵣ_
  ; isEquivalence to ≈ᵣ-isEquivalence
  ; setoid        to FinRoute-setoid
  )
open PermutationEq FinRoute-setoid public
open PermutationProperties FinRoute-setoid using (↭-decSetoid)

--------------------------------------------------------------------------------
-- Routing vector

RoutingVector : Set a
RoutingVector = Vector RoutingSet n

Øᵥ : RoutingVector
Øᵥ i = Ø

≈ᵥ-decSetoid : DecSetoid _ _
≈ᵥ-decSetoid = decSetoidᵥ (↭-decSetoid _≟ᵣ_) n

open DecSetoid ≈ᵥ-decSetoid public using ()
  renaming
  ( _≈_           to _≈ᵥ_
  ; reflexive     to ≈ᵥ-reflexive
  ; refl          to ≈ᵥ-refl
  ; sym           to ≈ᵥ-sym
  ; trans         to ≈ᵥ-trans
  ; isEquivalence to ≈ᵥ-isEquivalence
  ; setoid        to 𝕍ₛ
  )

--------------------------------------------------------------------------------
-- Auxilaries

IsInvalid : Pred (Fin n × Route) _
IsInvalid (d , v) = v ≈ ∞#

IsInvalid? : Decidable IsInvalid
IsInvalid? (d , v) = v ≟ ∞#

IsValid : Pred (Fin n × Route) _
IsValid = ∁ IsInvalid

IsValid? : Decidable IsValid
IsValid? p = ¬? (IsInvalid? p)

≤₂-decTotalOrder : DecTotalOrder a ℓ ℓ
≤₂-decTotalOrder = ×-decTotalOrder (Finₚ.≤-decTotalOrder n) ≤₊-decTotalOrder

open DecTotalOrder ≤₂-decTotalOrder public
  using () renaming
  ( _≤_             to _≤₂_
  ; _≤?_            to _≤₂?_
  ; isPreorder      to ≤₂-isPreorder
  ; totalOrder      to ≤₂-totalOrder
  ; isDecTotalOrder to ≤₂-isDecTotalOrder)

_<₂_ : Rel (Fin n × Route) _
_<₂_ = _<ₗₑₓ_ _≈ᵣ_ _≤₂_

<₂-isStrictTotalOrder : IsStrictTotalOrder _≈ᵣ_ _<₂_
<₂-isStrictTotalOrder = <-isStrictTotalOrder₂ _≈ᵣ_ _≤₂_ ≤₂-isDecTotalOrder

<₂-strictTotalOrder : StrictTotalOrder a ℓ ℓ
<₂-strictTotalOrder = record
  { Carrier            = Fin n × Route
  ; _≈_                = _≈ᵣ_
  ; _<_                = _<₂_
  ; isStrictTotalOrder = <₂-isStrictTotalOrder
  }
 
open StrictTotalOrder <₂-strictTotalOrder public
  using () renaming (compare to <₂-cmp)

_⊕₂_ : Op₂ (Fin n × Route)
(d₁ , v₁) ⊕₂ (d₂ , v₂) = (d₁ , v₁ ⊕ v₂)

mergeSorted : Op₂ RoutingSet
mergeSorted = partialMerge <₂-cmp _⊕₂_

--------------------------------------------------------------------------------
-- Definitions

-- Remove invalid routes
infix 11 _†
_† : RoutingSet → RoutingSet
xs † = filter IsValid? xs

-- Set addition
infixl 10 _⊕ₛ_
_⊕ₛ_ : Op₂ RoutingSet
S₁ ⊕ₛ S₂ = mergeSorted (sort S₁) (sort S₂)
  where open Sort ≤₂-decTotalOrder using (sort)

-- Vector addition
infixl 9 _⊕ᵥ_
_⊕ᵥ_ : Op₂ RoutingVector
(V₁ ⊕ᵥ V₂) i = (V₁ i) ⊕ₛ (V₂ i)

-- Big addition
infix 5 ⨁ₛ
⨁ₛ : ∀ {k} → (Fin k → RoutingSet) → RoutingSet
⨁ₛ iter = foldr _⊕ₛ_ Ø (tabulate iter)

-- Matrix to vector-of-sets transformation (Gamma_0 to Gamma_1)
infix 12 ~_
~_ : RoutingMatrix → RoutingVector
(~ M) i = (tabulate λ j → (j , M i j)) †

map₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B) → List (C × A) → List (C × B)
map₂ f = map (Prod.map₂ f)

-- Function application to sets
infix 13 _[_]
_[_] : (Route → Route) → RoutingSet → RoutingSet
f [ X ] = (map₂ f X) †

-- Matrix application to vector-of-sets
infix 10 _〚_〛
_〚_〛 : AdjacencyMatrix → RoutingVector → RoutingVector
(A 〚 V 〛) i = ⨁ₛ (λ q → (A i q ▷_) [ V q ])

--------------------------------------
-- Asynchronous

-- Lookup of destinations
lookup-d : RoutingSet → Fin n → Route
lookup-d []            j = ∞#
lookup-d ((d , s) ∷ S) j with d ≟F j
... | yes _ = s
... | no _  = lookup-d S j

-- Vector-of-sets to matrix transformation (Gamma_1 to Gamma_0)
infix 12 ─_
─_ : RoutingVector → RoutingMatrix
(─ V) i j = lookup-d (V i) j
