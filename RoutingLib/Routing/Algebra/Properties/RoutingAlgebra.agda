--------------------------------------------------------------------------------
-- Agda routing library
--
-- Properties of routing algebras
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Properties.RoutingAlgebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  where

import Algebra.Definitions as AlgebraDefinitions
import Algebra.Structures as AlgebraStructures
import Algebra.FunctionProperties.Consequences as Consequences
open import Algebra.Bundles
open import Algebra.FunctionProperties.Consequences.Propositional using (sel⇒idem)
open import Data.Product using (proj₁; _,_)
open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Level using (lift)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (DecTotalOrder; StrictTotalOrder; Maximum; Minimum)
import Relation.Binary.Construct.Converse as Converse
import Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Routing algebra
open import RoutingLib.Algebra.Bundles
open import RoutingLib.Algebra.Structures
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict as NSTS
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.DecTotalOrder as NonStrictToStrict

open import RoutingLib.Data.FiniteSet using (⟦_∣_⟧) renaming (FiniteSet to FiniteSet⁺)
open import RoutingLib.Relation.Binary

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open AlgebraDefinitions _≈_
open AlgebraStructures _≈_

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

⊕-isDecMonoid : IsDecMonoid _≈_ _⊕_ ∞#
⊕-isDecMonoid = record
  { isMonoid = ⊕-isMonoid
  ; _≟_      = _≟_
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
<₊-minimum = NSTS.<-min _≈_ _≤₊_ ≤₊-minimum

<₊-maximum : StrictMaximum _≈_ _<₊_ ∞#
<₊-maximum = NSTS.<-max _≈_ _≤₊_ ≈-sym ≤₊-maximum

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

--------------------------------------------------------------------------------
-- If the algebra is strictly increasing it's also increasing

strIncr⇒incr : IsStrictlyIncreasing algebra → IsIncreasing algebra
strIncr⇒incr strIncr f x with x ≟ ∞#
... | no  x≉∞ = proj₁ (strIncr f x≉∞)
... | yes x≈∞ = ≈-sym (begin
  (f ▷ x)  ⊕ x  ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
  (f ▷ ∞#) ⊕ ∞# ≈⟨ ⊕-congʳ (▷-fixedPoint f) ⟩
  ∞#       ⊕ ∞# ≈⟨ ⊕-idem ∞# ⟩
  ∞#            ≈⟨ ≈-sym x≈∞ ⟩
  x             ∎)
  where open EqReasoning S

-- If the algebra is strictly increasing then there is no cyclic set of routes
postulate strIncr⇒∄cyclic : IsStrictlyIncreasing algebra →
                  ∀ {n} (A : AdjacencyMatrix n) X → ¬ Cyclic _ A X
{-
strIncr⇒∄cyclic strInc A ⟦ zero  ∣ X ⟧ cyclic with cyclic 0F
... | (k , j , AₖⱼX₀≤X₀) = ≤₊⇒≯₊ AₖⱼX₀≤X₀ (strInc (A k j) {!!})
strIncr⇒∄cyclic strInc A ⟦ suc n ∣ X ⟧ cyclic =
  strIncr⇒∄cyclic strInc A ⟦ n ∣ X ∘ suc ⟧ (λ i → {!!})
-}

-- If the algebra is strictly increasing then every topology is cycle-free
strIncr⇒cycleFree : IsStrictlyIncreasing algebra →
                    ∀ {n} (A : AdjacencyMatrix n) → CycleFree _ A
strIncr⇒cycleFree strIncr A X cyclic = strIncr⇒∄cyclic strIncr A X cyclic

--------------------------------------------------------------------------------
-- kᵗʰ-level distributivity properties

isLevelDistrib-shrink : ∀ k {w x y z} → w ≤₊ x → x ≤₊ z → z ≤₊ y →
                        Level_DistributiveIn[_,_]Alt algebra k w y →
                        Level_DistributiveIn[_,_]Alt algebra k x z
isLevelDistrib-shrink zero    w≤x x≤z z≤y (lift w≈y) = lift (≤₊-antisym x≤z (≤₊-trans z≤y (≤₊-respˡ-≈ w≈y w≤x)))
isLevelDistrib-shrink (suc k) {w} {x} {y} {z} w≤x _ z≤y distrib f x≤u u≤z x≤v v≤z =
  (distrib f
    (≤₊-trans w≤x x≤u)
    (≤₊-trans u≤z z≤y)
    (≤₊-trans w≤x x≤v)
    (≤₊-trans v≤z z≤y))

isLevelDistrib-equal : ∀ k {x y} → x ≈ y → Level_DistributiveIn[_,_]Alt algebra k x y 
isLevelDistrib-equal zero    {_} {_} x≈y = lift x≈y
isLevelDistrib-equal (suc k) {x} {y} x≈y f {u} {v} x≤u u≤y x≤v v≤y =
  isLevelDistrib-equal k (begin
    f ▷ (u ⊕ v)       ≈⟨ ▷-cong f (⊕-congˡ (≈-sym u≈v)) ⟩
    f ▷ (u ⊕ u)       ≈⟨ ▷-cong f (⊕-idem u) ⟩
    f ▷ u             ≈⟨ ≈-sym (⊕-idem (f ▷ u)) ⟩
    (f ▷ u) ⊕ (f ▷ u) ≈⟨ ⊕-congˡ (▷-cong f u≈v) ⟩
    (f ▷ u) ⊕ (f ▷ v) ∎)
    where
    open EqReasoning S
    u≈v : u ≈ v
    u≈v = begin
      u  ≈⟨ ≤₊-antisym (≤₊-respʳ-≈ (≈-sym x≈y) u≤y) x≤u ⟩
      x  ≈⟨ ≤₊-antisym x≤v (≤₊-respʳ-≈ (≈-sym x≈y) v≤y) ⟩
      v  ∎


------------------------------------------------------------------------------
-- Other

r≈∞⇒f▷r≈∞ : ∀ {n} {i j : Fin n} {f : Step i j} {r} → r ≈ ∞# → f ▷ r ≈ ∞#
r≈∞⇒f▷r≈∞ {f = f} {r} r≈∞ = ≈-trans (▷-cong _ r≈∞) (▷-fixedPoint f)

f▷r≉∞⇒r≉∞ : ∀ {n} {i j : Fin n} {f : Step i j} {r} → f ▷ r ≉ ∞# → r ≉ ∞#
f▷r≉∞⇒r≉∞ f▷r≉∞ r≈∞ = f▷r≉∞ (r≈∞⇒f▷r≈∞ r≈∞)
