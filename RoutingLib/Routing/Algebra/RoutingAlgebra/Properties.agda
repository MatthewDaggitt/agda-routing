open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties as FunctionProperties
import Algebra.FunctionProperties.Consequences as Consequences
open import Algebra.FunctionProperties.Consequences using (sel⇒idem)
open import Data.Product using (proj₁)
open import Data.Fin using (Fin)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (DecTotalOrder; StrictTotalOrder)
import Relation.Binary.EqReasoning as EqReasoning

import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder
import RoutingLib.Relation.Binary.NonStrictToStrict.DecTotalOrder as NonStrictToStrict
import RoutingLib.Relation.Binary.Flip as Flip

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra

module RoutingLib.Routing.Algebra.RoutingAlgebra.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
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
  ; <-≤-trans to <-≤₊-trans
  ; ≤-<-trans to ≤-<₊-trans
  ; <⇒≱       to <₊⇒≱₊
  ; ≤⇒≯       to ≤₊⇒≯₊
  ; ≰⇒>       to ≰₊⇒>₊
  ; <-asym    to <₊-asym
  ; <-respʳ-≈ to <₊-respʳ-≈
  ; <-respˡ-≈ to <₊-respˡ-≈
  ; <-strictPartialOrder to <₊-strictPartialOrder
  ; <-strictTotalOrder   to <₊-strictTotalOrder
  )


--------------------------------------------------------------------------------
-- Strictly increasing routing algebras

strIncr⇒incr : IsStrictlyIncreasing algebra → IsIncreasing algebra
strIncr⇒incr strIncr f x with x ≟ ∞
... | no  x≉∞ = proj₁ (strIncr f x≉∞)
... | yes x≈∞ = begin
  (f ▷ x) ⊕ x ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
  (f ▷ ∞) ⊕ ∞ ≈⟨ ⊕-cong (▷-fixedPoint f) ≈-refl ⟩
  ∞       ⊕ ∞ ≈⟨ sel⇒idem S ⊕-sel ∞ ⟩
  ∞           ≈⟨ ≈-sym x≈∞ ⟩
  x           ∎
  where open EqReasoning S

------------------------------------------------------------------------------
-- Other

r≈∞⇒f▷r≈∞ : ∀ {n} {i j : Fin n} {f : Step i j} {r} → r ≈ ∞ → f ▷ r ≈ ∞
r≈∞⇒f▷r≈∞ {f = f} {r} r≈∞ = ≈-trans (▷-cong _ r≈∞) (▷-fixedPoint f)

f▷r≉∞⇒r≉∞ : ∀ {n} {i j : Fin n} {f : Step i j} {r} → f ▷ r ≉ ∞ → r ≉ ∞
f▷r≉∞⇒r≉∞ f▷r≉∞ r≈∞ = f▷r≉∞ (r≈∞⇒f▷r≈∞ r≈∞)
