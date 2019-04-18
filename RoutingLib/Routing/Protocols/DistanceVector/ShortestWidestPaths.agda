--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the definition of the algebra underlying a distance
-- vector protocol that solves the shortest-widest paths problem, i.e. tries to
-- choose the highest bandwidth path and breaks ties based on path length.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.DistanceVector.ShortestWidestPaths where

open import Algebra.FunctionProperties using (Op₂)

open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties
open import RoutingLib.Data.Path.Uncertified

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Construct.Lex
  as Lex using (Lex)

open import RoutingLib.Routing.Protocols.DistanceVector.ShortestPaths
  as Shortest using (Aˢʰᵒʳᵗᵉˢᵗ)
open import RoutingLib.Routing.Protocols.DistanceVector.WidestPaths
  as Widest using (Aʷⁱᵈᵉˢᵗ)

Aˢʷ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aˢʷ = Lex Aʷⁱᵈᵉˢᵗ Aˢʰᵒʳᵗᵉˢᵗ

isRoutingAlgebra : IsRoutingAlgebra Aˢʷ
isRoutingAlgebra = Lex.isRoutingAlgebra Aʷⁱᵈᵉˢᵗ Aˢʰᵒʳᵗᵉˢᵗ Widest.isRoutingAlgebra Shortest.isRoutingAlgebra

{-
------------------------------------------------------------------------
-- Algebra

Route : Set
Route = ℕ∞ × ℕ∞

Step : ∀ {n} (i j : Fin n) → Set
Step i j = ℕ∞ × ℕ∞

open Data.Maybe public renaming (nothing to invalid; just to valid)

0# : Route
0# = ∞ , N 0

∞# : Route
∞# = N 0 , ∞

_⊕_ : Op₂ Route
_⊕_ = Lex _≟_ _⊔_ _⊓_

_▷_ : ∀ {n} {i j : Fin n} → Step i j → Route → Route 
(u , v) ▷ (x , y) = u ⊓ x , v + y

f∞ : ∀ {n} (i j : Fin n) → Step i j
f∞ i j = N 0 , ∞

f∞-reject : ∀ {n} (i j : Fin n) x → _▷_ {i = i} {j} (f∞ i j) x ≡ ∞#
f∞-reject i j x = cong₂ _,_ (⊓-zeroˡ _) refl

_≟R_ : Decidable (_≡_ {A = Route})
(a , x) ≟R (b , y) with a ≟ b | x ≟ y
... | no a≢b   | _        = no λ { refl → a≢b refl }
... | _        | no  x≢y  = no λ { refl → x≢y refl }
... | yes refl | yes refl = yes refl

isDecEquivalence : IsDecEquivalence {A = Route} _≡_
isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟R_
  }

Aˢʷ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aˢʷ = record
  { Route = Route
  ; Step = Step
  ; _≈_ = _≡_
  ; _⊕_ = _⊕_
  ; _▷_ = λ {n} {i} {j} → _▷_ {n} {i} {j}
  ; 0# = 0#
  ; ∞# = ∞#
  ; f∞ = f∞
  ; ≈-isDecEquivalence = isDecEquivalence
  ; ⊕-cong = cong₂ _⊕_
  ; ▷-cong = λ {n} {i} {j} f → cong (_▷_ {n} {i} {j} f)
  ; f∞-reject = f∞-reject
  }
-} 
