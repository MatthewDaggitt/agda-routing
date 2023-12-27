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
open import Relation.Binary.Construct.NonStrictToStrict
  using (<-isStrictTotalOrder₂) renaming (_<_ to _<ₗₑₓ_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no; ¬_; does; proof)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Data.Product as Prod using (_×_; _,_)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.Routing.Prelude as RoutingPrelude
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebra

open import RoutingLib.Data.List using (partialMerge)
import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties

module RoutingLib.lmv34.Synchronous.Gamma_one.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open RoutingPrelude algebra n
open RawRoutingAlgebra algebra
open RoutingAlgebra isRoutingAlgebra using (≤₊-decTotalOrder)


map₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B) → List (C × A) → List (C × B)
map₂ f = map (Prod.map₂ f)

--------------------------------------------------------------------------------
-- Assignments

open import RoutingLib.Routing.Basics.Assignment algebra n public
open import RoutingLib.Routing.Basics.Assignment.Properties isRoutingAlgebra n public

_⊕ₐ_ : Op₂ Assignment
(d₁ , v₁) ⊕ₐ (d₂ , v₂) = (d₁ , v₁ ⊕ v₂)

--------------------------------------------------------------------------------
-- Routing sets
--------------------------------------------------------------------------------
-- Definition

RoutingSet : Set a
RoutingSet = List Assignment

--------------------------------------------------------------------------------
-- Examples

Ø : RoutingSet
Ø = []

--------------------------------------------------------------------------------
-- Equality over routing sets

open PermutationEq 𝔸ₛ public
open PermutationProperties 𝔸ₛ using (↭-decSetoid)

--------------------------------------------------------------------------------
-- Operations

-- Remove invalid routes
infix 11 _†
_† : RoutingSet → RoutingSet
xs † = filter IsValid? xs

mergeSorted : Op₂ RoutingSet
mergeSorted = partialMerge <ₐₜ-cmp _⊕ₐ_

-- Set addition
infixl 10 _⊕ₛ_
_⊕ₛ_ : Op₂ RoutingSet
S₁ ⊕ₛ S₂ = mergeSorted (sort S₁) (sort S₂)
  where open Sort ≤ₐₜ-decTotalOrder using (sort)

-- Big addition
infix 5 ⨁ₛ
⨁ₛ : ∀ {k} → (Fin k → RoutingSet) → RoutingSet
⨁ₛ iter = foldr _⊕ₛ_ Ø (tabulate iter)

-- Function application to sets
infix 13 _[_]
_[_] : (PathWeight → PathWeight) → RoutingSet → RoutingSet
f [ X ] = (map₂ f X) †

-- Lookup of destinations
lookup-d : RoutingSet → Node → PathWeight
lookup-d []            j = ∞#
lookup-d ((d , s) ∷ S) j with d ≟F j
... | yes _ = s
... | no _  = lookup-d S j

--------------------------------------------------------------------------------
-- Routing vector
--------------------------------------------------------------------------------
-- Definition

RoutingVector : Set a
RoutingVector = Vector RoutingSet n

--------------------------------------------------------------------------------
-- Examples

Øᵥ : RoutingVector
Øᵥ i = Ø

--------------------------------------------------------------------------------
-- Equality over routing vectors

≈ᵥ-decSetoid : DecSetoid _ _
≈ᵥ-decSetoid = decSetoidᵥ (↭-decSetoid _≟ₐ_) n

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
-- Definitions

-- Vector addition
infixl 9 _⊕ᵥ_
_⊕ᵥ_ : Op₂ RoutingVector
(V₁ ⊕ᵥ V₂) i = (V₁ i) ⊕ₛ (V₂ i)

-- Matrix to vector-of-sets transformation (Gamma_0 to Gamma_1)
infix 12 ~_
~_ : RoutingMatrix → RoutingVector
(~ M) i = (tabulate λ j → (j , M i j)) †

-- Matrix application to vector-of-sets
infix 10 _〚_〛
_〚_〛 : AdjacencyMatrix → RoutingVector → RoutingVector
(A 〚 V 〛) i = ⨁ₛ (λ q → (A i q ▷_) [ V q ])

-- Vector-of-sets to matrix transformation (Gamma_1 to Gamma_0)
infix 12 ─_
─_ : RoutingVector → RoutingMatrix
(─ V) i j = lookup-d (V i) j
