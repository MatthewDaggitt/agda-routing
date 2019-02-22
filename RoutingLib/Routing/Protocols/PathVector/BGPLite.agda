--------------------------------------------------------------------------------
-- A specification of a path-vector routing protocol that shares many
-- similarities with the Border Gateway Protocol (BGP), including local
-- preferences, conditional policy, community values, path inflation and more.
--
-- Unlike BGP this algebra is strictly increasing as the local preference value
-- cannot be set arbitarily. In addition it does not implement the MED attribute
-- that violates associativity.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.PathVector.BGPLite where

open import Algebra.FunctionProperties
open import Data.Nat using (ℕ; _≟_)
open import Data.Nat.Properties using () renaming (<-cmp to compare)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; isEquivalence)
open import Level using () renaming (zero to ℓ₀; suc to lsuc)

import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder as NaturalChoice

open import RoutingLib.Data.Path.Uncertified using (Path; []; _∷_; inflate; deflate; length)
open import RoutingLib.Data.Path.Uncertified.Properties

open import RoutingLib.Routing.Algebra

--------------------------------------------------------------------------------
-- Definition of the underlying routing problem (i.e. routing algebra)

open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Policy
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Communities
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Route

data Step {n} (i j : Fin n) : Set₁ where
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
_▷_ : ∀ {n} {i j : Fin n} → Step i j → Route → Route
_▷_ {_} {_} {_} _          invalid       = invalid
_▷_ {_} {i} {j} (step pol) (valid x c p) with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
... | no  _    | _       = invalid
... | yes _    | yes _   = invalid
... | yes ij⇿p | no  i∈p = apply pol (valid x c ((toℕ i , toℕ j) ∷ p))

f∞ : ∀ {n} (i j : Fin n) → Step i j
f∞ i j = step reject

▷-cong : ∀ {n} {i j : Fin n} (f : Step i j) {r s} → r ≡ s → f ▷ r ≡ f ▷ s
▷-cong f refl = refl

⊕-cong : Congruent₂ _≡_ _⊕_
⊕-cong = cong₂ _⊕_

f∞-reject : ∀ {n : ℕ} (i j : Fin n) (x : Route) → f∞ i j ▷ x ≡ invalid
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
