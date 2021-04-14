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
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?; ¬-reflects)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary as U using (Pred; _∈_; ∁)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict


open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Assignment
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)
  where

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Definition

Assignment : Set a
Assignment = Fin n × Route

--------------------------------------------------------------------------------
-- Functions

node : Assignment → Fin n
node = proj₁

value : Assignment → Route
value = proj₂

--------------------------------------------------------------------------------
-- Predicates

IsInvalid : Pred Assignment ℓ
IsInvalid (d , v) = v ≈ ∞#

IsInvalid? : U.Decidable IsInvalid
IsInvalid? (d , v) = v ≟ ∞#

IsValid : Pred Assignment ℓ
IsValid = ∁ IsInvalid

IsValid? : U.Decidable IsValid
IsValid? p = ¬? (IsInvalid? p)

--------------------------------------------------------------------------------
-- Equality relation

Dec𝔸ₛ : DecSetoid a ℓ
Dec𝔸ₛ = DirectProduct.×-decSetoid (Fin.≡-decSetoid n) DS

open DecSetoid Dec𝔸ₛ public
  using () renaming
  ( _≈_           to _≈ₐ_
  ; _≉_           to _≉ₐ_
  ; refl          to ≈ₐ-refl
  ; trans         to ≈ₐ-trans
  ; sym           to ≈ₐ-sym
  ; _≟_           to _≟ₐ_
  ; isEquivalence to ≈ₐ-isEquivalence
  ; setoid        to 𝔸ₛ
  )

--------------------------------------------------------------------------------
-- Partial ordering relation

-- In this ordering, only assignments to the same node may be compared.

_≤ₐₚ_ : Rel Assignment ℓ
_≤ₐₚ_ = DirectProduct.Pointwise _≡_ _≤₊_

_≤ₐₚ?_ : Decidable _≤ₐₚ_
_≤ₐₚ?_ = DirectProduct.×-decidable Fin._≟_ _≤₊?_

--------------------------------------------------------------------------------
-- Total ordering relation

-- In this ordering, all assignments may be compared

_≤ₐₜ_ : Rel Assignment ℓ
_≤ₐₜ_ = LexProduct.×-Lex _≡_ Fin._≤_ _≤₊_

_<ₐₜ_ : Rel Assignment ℓ
_<ₐₜ_ = NonStrictToStrict._<_ _≈ₐ_ _≤ₐₜ_

_≤ₐₜ?_ : Decidable _≤ₐₜ_
_≤ₐₜ?_ = LexProduct.×-decidable Fin._≟_ Fin._≤?_ _≤₊?_

_<ₐₜ?_ : Decidable _<ₐₜ_
_<ₐₜ?_ = NonStrictToStrict.<-decidable _ _ _≟ₐ_ _≤ₐₜ?_
