--------------------------------------------------------------------------------
-- Agda routing library
--
-- Core definition of the BGPLite protocol
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.BGPLite.Core where

import Algebra.Construct.NaturalChoice.Min as NaturalChoice
open import Algebra
open import Data.Nat using (ℕ; _≟_)
open import Data.Nat.Properties using () renaming (<-cmp to compare)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; isEquivalence)
import Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
open import Level using (0ℓ) renaming (suc to lsuc)

open import RoutingLib.Data.Path.Uncertified
  using (Path; []; _∷_; inflate; deflate; length)
open import RoutingLib.Data.Path.Uncertified.Properties

open import RoutingLib.Routing.Algebra

private
  variable
    n : ℕ
    i j : Fin n

--------------------------------------------------------------------------------
-- Definition of the underlying routing problem (i.e. routing algebra)

open import RoutingLib.Routing.Protocols.BGPLite.Policies
open import RoutingLib.Routing.Protocols.BGPLite.Communities
open import RoutingLib.Routing.Protocols.BGPLite.Routes

data Step (i j : Fin n) : Set₁ where
  step : Policy → Step i j

0# : Route
0# = valid 0 ∅ []

∞# : Route
∞# = invalid

infix 5 _⊕_
_⊕_ : Op₂ Route
x@invalid        ⊕ y            = y
x                ⊕ y@invalid    = x
x@(valid l cs p) ⊕ y@(valid m ds q) with compare l m
... | tri< x<y _ _  = x
... | tri> _ _ y<x  = y
... | tri≈ _ x=y _  with compare (length p) (length q)
...   | tri< |p|<|q| _ _  = x
...   | tri> _ _ |q|<|p|  = y
...   | tri≈ _ |p|=|q| _  with p ≤ₗₑₓ? q
...     | yes p≤q = x
...     | no  q≤p = y

infix 5 _▷_
_▷_ : Step i j → Route → Route
_▷_ {_} {_} {_} _          invalid       = invalid
_▷_ {_} {i} {j} (step pol) (valid x c p) with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
... | no  _    | _       = invalid
... | yes _    | yes _   = invalid
... | yes ij⇿p | no  i∈p = apply pol (valid x c ((toℕ i , toℕ j) ∷ p))

f∞ : ∀ (i j : Fin n) → Step i j
f∞ i j = step reject

▷-cong : ∀ (f : Step i j) {r s} → r ≡ s → f ▷ r ≡ f ▷ s
▷-cong f refl = refl

⊕-cong : Congruent₂ _≡_ _⊕_
⊕-cong = cong₂ _⊕_

f∞-reject : ∀ (i j : Fin n) (x : Route) → f∞ i j ▷ x ≡ invalid
f∞-reject i j invalid        = refl
f∞-reject i j (valid l cs p) with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
... | no  _    | _       = refl
... | yes _    | yes _   = refl
... | yes ij⇿p | no  i∈p = refl

A : RawRoutingAlgebra _ _ _
A = record
  { Step               = Step
  ; Route              = Route
  ; _≈_                = _≡_
  ; _⊕_                = _⊕_
  ; _▷_                = _▷_
  ; 0#                 = 0#
  ; ∞#                 = ∞#
  ; f∞                 = f∞
  ; f∞-reject          = f∞-reject
  ; ≈-isDecEquivalence = ≡ᵣ-isDecEquivalence
  ; ▷-cong             = ▷-cong
  ; ⊕-cong             = ⊕-cong
  }

--------------------------------------------------------------------------------
-- Definition of the routing protocol

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule using (𝕋; Schedule)
open import RoutingLib.Routing A
  using (Network; RoutingMatrix; AdjacencyMatrix; I)
import RoutingLib.Routing.VectorBased.Asynchronous A as AsyncRouting
import RoutingLib.Routing.VectorBased.Synchronous  A as SyncRouting

-- Synchronous version (can start from any initial state)
σ : ∀ {n} → AdjacencyMatrix n → RoutingMatrix n → 𝕋 → RoutingMatrix n
σ {n} A X₀ t = SyncRouting.σ A t X₀

-- Dynamic asynchronous version (starts identity matrix but has arbitrary
-- network growth and failures depending on the exact schedule and network)
δ : ∀ {n} → Network n → Schedule n → 𝕋 → RoutingMatrix n
δ {n} N ψ = AsyncRouting.δ N ψ (I n)
