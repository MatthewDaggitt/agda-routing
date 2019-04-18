--------------------------------------------------------------------------------
-- Agda routing library
--
-- Defines another algebra that is slightly better behaved than that of the main
-- BGPLite algebra. It is however identical in operation. This allows the
-- BGPLite algebra to be proved convergent via this algebra being shown to be
-- convergent.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.PathVector.BGPLite.Simulation where

import Algebra.Construct.NaturalChoice.Min as Min
open import Data.Maybe using (just; nothing; Is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; <-cmp; <-transˡ)
open import Data.List.Properties using (∷-injectiveˡ)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Data.Product.Properties.WithK using (,-injectiveʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_; _$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.UncertifiedI using (Path; Pathᵛ; invalid; valid; source; sourceᵥ)
open import RoutingLib.Data.Path.UncertifiedI.Properties using (valid-injective)
open import RoutingLib.Data.Path.Uncertified using ([]; _∷_; inflate; deflate; length; _⇿_; _∈ₚ_)
open import RoutingLib.Data.Path.Uncertified.Properties

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Main
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Policy
  using (apply; apply-result)
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Route
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Communities

open ≡-Reasoning

private
  variable
    n : ℕ
    i j : Fin n
    r : Route
    p q : Pathᵛ

--------------------------------------------------------------------------------
-- The simulating algebra
--
-- The algebra is identical to the algebra of BGPLite except for a different
-- choice operator. This new operator is fully associative, rather than just
-- associative over comparable routes. As proving associativity of an operator
-- requires O(n³) cases, this is instead implemented via the natural choice
-- operation for the associated total order. The order can be proved to be
-- transitive in O(n²) operations, and hence the operator is transitive.

open Min ≤ᵣ-totalOrder public
  using () renaming (_⊓_ to _⊕ₐₗₜ_; ⊓-cong to ⊕ₐₗₜ-cong)

Aₐₗₜ : RawRoutingAlgebra _ _ _
Aₐₗₜ = record
  { Route              = Route
  ; Step               = Step
  ; _≈_                = _≡_
  ; _⊕_                = _⊕ₐₗₜ_
  ; _▷_                = _▷_
  ; 0#                 = 0#
  ; ∞#                 = ∞#
  ; f∞                 = f∞
  ; ≈-isDecEquivalence = ≡ᵣ-isDecEquivalence
  ; ⊕-cong             = ⊕ₐₗₜ-cong
  ; ▷-cong             = ▷-cong
  ; f∞-reject          = f∞-reject
  }
