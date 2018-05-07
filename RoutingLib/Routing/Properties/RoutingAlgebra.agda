open import Algebra.Structures
import Algebra.FunctionProperties as FunctionProperties
import Algebra.FunctionProperties.Consequences as Consequences
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (DecTotalOrder; StrictTotalOrder)
import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder

open import RoutingLib.Algebra
open import RoutingLib.Algebra.Structures
import RoutingLib.Relation.Binary.NonStrictToStrict.DecTotalOrder as NonStrictToStrict
import RoutingLib.Relation.Binary.Flip as Flip

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Properties.RoutingAlgebra
  {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ) where

open RoutingAlgebra 𝓡𝓐
open FunctionProperties _≈_

------------------------------------------------------------------------------
-- Additional properties of ⊕ and ▷

⊕-idem : Idempotent _⊕_
⊕-idem = Consequences.sel⇒idem S ⊕-sel

⊕-identityˡ : LeftIdentity ∞ _⊕_
⊕-identityˡ x = ≈-trans (⊕-comm ∞ x) (⊕-identityʳ x)

⊕-isSemigroup : IsSemigroup _≈_ _⊕_
⊕-isSemigroup = record
  { isEquivalence = ≈-isEquivalence
  ; assoc         = ⊕-assoc
  ; ∙-cong        = ⊕-cong
  }

⊕-isBand : IsBand _≈_ _⊕_
⊕-isBand = record
  { isSemigroup = ⊕-isSemigroup
  ; idem        = ⊕-idem
  }

⊕-isSemilattice : IsSemilattice _≈_ _⊕_
⊕-isSemilattice = record
  { isBand = ⊕-isBand
  ; comm   = ⊕-comm
  }

⊕-semilattice : Semilattice _ _
⊕-semilattice = record
  { isSemilattice = ⊕-isSemilattice
  }

------------------------------------------------------------------------------
-- The induced right natural ordering over routes

≤₊-decTotalOrder : DecTotalOrder b ℓ ℓ
≤₊-decTotalOrder =
  RightNaturalOrder.≤-decTotalOrder _≈_ _⊕_ ⊕-isSemigroup _≟_ ⊕-comm ⊕-sel

≥₊-decTotalOrder : DecTotalOrder _ _ _
≥₊-decTotalOrder = Flip.decTotalOrderᵘ ≤₊-decTotalOrder
    
open DecTotalOrder ≤₊-decTotalOrder public
  using ()
  renaming
  ( _≤?_            to _≤₊?_
  ; refl            to ≤₊-refl
  ; reflexive       to ≤₊-reflexive
  ; trans           to ≤₊-trans
  ; antisym         to ≤₊-antisym
  ; poset           to ≤₊-poset
  ; total           to ≤₊-total
  ; ≤-resp-≈        to ≤₊-resp-≈
  ; totalOrder      to ≤₊-totalOrder
  ; isDecTotalOrder to ≤₊-isDecTotalOrder
  )

open NonStrictToStrict ≤₊-decTotalOrder public
  using ()
  renaming
  ( _<?_      to _<₊?_
  ; <≤-trans  to <≤₊-trans
  ; ≤<-trans  to ≤<₊-trans
  ; <⇒≱       to <₊⇒≱₊
  ; ≤⇒≯       to ≤₊⇒≯₊
  ; ≰⇒>       to ≰₊⇒>₊
  ; <-asym    to <₊-asym
  ; <-respʳ-≈ to <₊-respʳ-≈
  ; <-respˡ-≈ to <₊-respˡ-≈
  ; <-strictPartialOrder to <₊-strictPartialOrder
  ; <-strictTotalOrder   to <₊-strictTotalOrder
  )

------------------------------------------------------------------------------
-- Other
    
r≈∞⇒e▷r≈∞ : ∀ {e r} → r ≈ ∞ → e ▷ r ≈ ∞
r≈∞⇒e▷r≈∞ {e} {r} r≈∞ = ≈-trans (▷-cong _ r≈∞) (▷-zero e)

e▷r≉∞⇒r≉∞ : ∀ {e r} → e ▷ r ≉ ∞ → r ≉ ∞
e▷r≉∞⇒r≉∞ e▷r≉∞ r≈∞ = e▷r≉∞ (r≈∞⇒e▷r≈∞ r≈∞)
