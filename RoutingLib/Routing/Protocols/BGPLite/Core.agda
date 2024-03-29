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
open import Data.Fin using (Fin; toℕ)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; isEquivalence)
import Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
open import Level using (0ℓ) renaming (suc to lsuc)

open import RoutingLib.Routing.Basics.Path.Uncertified
  using (Path; []; _∷_; inflate; deflate; length)
open import RoutingLib.Routing.Basics.Path.Uncertified.Properties

open import RoutingLib.Routing.Algebra

private
  variable
    n : ℕ
    i j : Fin n

--------------------------------------------------------------------------------
-- Definition of the underlying routing problem (i.e. routing algebra)

open import RoutingLib.Routing.Protocols.BGPLite.LocalPref
open import RoutingLib.Routing.Protocols.BGPLite.Policies
open import RoutingLib.Routing.Protocols.BGPLite.Communities
open import RoutingLib.Routing.Protocols.BGPLite.PathWeights

data Extension (i j : Fin n) : Set₁ where
  ext : Policy → Extension i j

0# : PathWeight
0# = valid 2⁸-1 ∅ []

∞# : PathWeight
∞# = invalid

infix 5 _⊕_
_⊕_ : Op₂ PathWeight
x@invalid        ⊕ y            = y
x                ⊕ y@invalid    = x
x@(valid l cs p) ⊕ y@(valid m ds q) with <ˡᵖ-compare l m
... | tri< x<y _ _  = y
... | tri> _ _ y<x  = x
... | tri≈ _ x=y _  with compare (length p) (length q)
...   | tri< |p|<|q| _ _  = x
...   | tri> _ _ |q|<|p|  = y
...   | tri≈ _ |p|=|q| _  with p ≤ₗₑₓ? q
...     | yes p≤q = x
...     | no  q≤p = y

infix 5 _▷_
_▷_ : Extension i j → PathWeight → PathWeight
_▷_ {_} {_} {_} _          invalid       = invalid
_▷_ {_} {i} {j} (ext pol) (valid x c p) with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
... | no  _    | _       = invalid
... | yes _    | yes _   = invalid
... | yes ij⇿p | no  i∈p = apply pol (valid x c ((toℕ i , toℕ j) ∷ p))

f∞ : ∀ (i j : Fin n) → Extension i j
f∞ i j = ext reject

▷-cong : ∀ (f : Extension i j) {r s} → r ≡ s → f ▷ r ≡ f ▷ s
▷-cong f refl = refl

⊕-cong : Congruent₂ _≡_ _⊕_
⊕-cong = cong₂ _⊕_

f∞-reject : ∀ (i j : Fin n) (x : PathWeight) → f∞ i j ▷ x ≡ invalid
f∞-reject i j invalid        = refl
f∞-reject i j (valid l cs p) with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
... | no  _    | _       = refl
... | yes _    | yes _   = refl
... | yes ij⇿p | no  i∈p = refl

A : RawRoutingAlgebra _ _ _
A = record
  { PathWeight         = PathWeight
  ; Step               = Extension
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
open import RoutingLib.Routing.Prelude A
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
