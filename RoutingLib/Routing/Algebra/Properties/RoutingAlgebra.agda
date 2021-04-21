--------------------------------------------------------------------------------
-- Agda routing library
--
-- Properties of routing algebras
--------------------------------------------------------------------------------

open import Algebra.Bundles
open import Algebra.Consequences.Propositional using (sel⇒idem)
open import Data.Product using (proj₁; _,_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Level using (lift)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (DecTotalOrder; StrictTotalOrder; Maximum; Minimum)
import Relation.Binary.Construct.Converse as Converse
import Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Relation.Binary
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict as NSTS
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.DecTotalOrder as NonStrictToStrict

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Properties.RoutingAlgebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_

------------------------------------------------------------------------------
-- _⊕_

⊕-idem : Idempotent _⊕_
⊕-idem x with ⊕-sel x x
... | inj₁ v = v
... | inj₂ v = v

⊕-identityˡ : LeftIdentity ∞# _⊕_
⊕-identityˡ x = ≈-trans (⊕-comm ∞# x) (⊕-identityʳ x)

⊕-identity : Identity ∞# _⊕_
⊕-identity = ⊕-identityˡ , ⊕-identityʳ

⊕-isSemigroup : IsSemigroup _⊕_
⊕-isSemigroup = record
  { isMagma = ⊕-isMagma
  ; assoc   = ⊕-assoc
  }

⊕-isBand : IsBand _⊕_
⊕-isBand = record
  { isSemigroup = ⊕-isSemigroup
  ; idem        = ⊕-idem
  }

⊕-isSemilattice : IsSemilattice _⊕_
⊕-isSemilattice = record
  { isBand = ⊕-isBand
  ; comm   = ⊕-comm
  }

⊕-semilattice : Semilattice _ _
⊕-semilattice = record
  { isSemilattice = ⊕-isSemilattice
  }

⊕-isMonoid : IsMonoid _⊕_ ∞#
⊕-isMonoid = record
  { isSemigroup = ⊕-isSemigroup
  ; identity    = ⊕-identity
  }

------------------------------------------------------------------------------
-- An ordering over routes is induced from ⊕ using the right natural order.
-- i.e. x ≤₊ y iff when choosing between x and y you choose x.

≤₊-decTotalOrder : DecTotalOrder a ℓ ℓ
≤₊-decTotalOrder = RightNaturalOrder.decTotalOrder _ _ ⊕-isSemilattice ⊕-sel _≟_

≥₊-decTotalOrder : DecTotalOrder _ _ _
≥₊-decTotalOrder = Converse.decTotalOrder ≤₊-decTotalOrder

≤₊-minimum : Minimum _≤₊_ 0#
≤₊-minimum x = ≈-sym (⊕-zeroʳ x)

≤₊-maximum : Maximum _≤₊_ ∞#
≤₊-maximum x = ≈-sym (⊕-identityˡ x)

<₊-minimum : StrictMinimum _≈_ _<₊_ 0#
<₊-minimum = NSTS.<-min _≈_ _≤₊_ ≈-sym ≤₊-minimum

<₊-maximum : StrictMaximum _≈_ _<₊_ ∞#
<₊-maximum = NSTS.<-max _≈_ _≤₊_ ≤₊-maximum

open DecTotalOrder ≤₊-decTotalOrder public
  using ()
  renaming
  ( refl            to ≤₊-refl
  ; reflexive       to ≤₊-reflexive
  ; trans           to ≤₊-trans
  ; antisym         to ≤₊-antisym
  ; total           to ≤₊-total
  ; ≤-resp-≈        to ≤₊-resp-≈
  ; poset           to ≤₊-poset
  ; totalOrder      to ≤₊-totalOrder
  ; isDecTotalOrder to ≤₊-isDecTotalOrder
  )

open NonStrictToStrict ≤₊-decTotalOrder public
  using ()
  renaming
  ( <-≤-trans to <-≤₊-trans
  ; ≤-<-trans to ≤-<₊-trans
  ; <⇒≉       to <₊⇒≉
  ; <⇒≤       to <₊⇒≤₊
  ; <⇒≱       to <₊⇒≱₊
  ; ≤⇒≯       to ≤₊⇒≯₊
  ; ≰⇒>       to ≰₊⇒>₊
  ; <-asym    to <₊-asym
  ; <-trans   to <₊-trans
  ; <-respʳ-≈ to <₊-respʳ-≈
  ; <-respˡ-≈ to <₊-respˡ-≈
  ; <-resp-≈  to <₊-resp-≈
  ; <-cmp     to <₊-cmp
  ; <-irrefl  to <₊-irrefl
  ; <-strictPartialOrder to <₊-strictPartialOrder
  ; <-strictTotalOrder   to <₊-strictTotalOrder
  )

------------------------------------------------------------------------------
-- Other

r≈∞⇒f▷r≈∞ : ∀ {n} {i j : Fin n} {f : Step i j} {r} → r ≈ ∞# → f ▷ r ≈ ∞#
r≈∞⇒f▷r≈∞ {f = f} {r} r≈∞ = ≈-trans (▷-cong _ r≈∞) (▷-fixedPoint f)

f▷r≉∞⇒r≉∞ : ∀ {n} {i j : Fin n} {f : Step i j} {r} → f ▷ r ≉ ∞# → r ≉ ∞#
f▷r≉∞⇒r≉∞ f▷r≉∞ r≈∞ = f▷r≉∞ (r≈∞⇒f▷r≈∞ r≈∞)
