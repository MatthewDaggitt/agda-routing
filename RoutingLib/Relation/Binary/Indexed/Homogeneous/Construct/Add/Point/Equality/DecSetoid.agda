open import Level
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec

open import RoutingLib.Relation.Nullary.Indexed.Construct.Add.Point
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.Add.Point.Equality as LiftedEquality

module RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.Add.Point.Equality.DecSetoid
  {a ℓ i} {I : Set i} (DS : IndexedDecSetoid I a ℓ) where

open IndexedDecSetoid DS

≈∙ᵢ-iDecSetoid : IndexedDecSetoid I a (a ⊔ i ⊔ ℓ)
≈∙ᵢ-iDecSetoid = record
  { isDecEquivalenceᵢ = LiftedEquality.≈∙ᵢ-isIDecEquivalence Carrierᵢ _≈ᵢ_ isDecEquivalenceᵢ
  }

open module Eq = LiftedEquality Carrierᵢ _≈ᵢ_ public
  using
  ( [≈]ᵢ-injective
  ; [≈]-injective
  ; [_]≈
  ; [_]ᵢ
  ; ∙≈ᵢ∙
  ; extractValueᵢ-cong
  ; extractValue-cong
  ; IsValueᵢ-resp-≈∙
  ; IsValue-resp-≈∙
  )

open IndexedDecSetoid ≈∙ᵢ-iDecSetoid public
  using ()
  renaming
  ( _≈ᵢ_              to _≈∙ᵢ_
  ; reflᵢ             to ≈∙ᵢ-refl
  ; symᵢ              to ≈∙ᵢ-sym
  ; transᵢ            to ≈∙ᵢ-trans
  ; _≟ᵢ_              to _≟∙ᵢ
  ; isDecEquivalenceᵢ to ≈∙ᵢ-isIDecEquivalence
  ; _≈_               to _≈∙_
  ; refl              to ≈∙-refl
  ; sym               to ≈∙-sym
  ; setoid            to ≈∙-setoid
  ; indexedSetoid     to ≈∙-setoidᵢ
  )

extract-IsValueᵢ : ∀ {i} {x : Pointedᵢ Carrierᵢ i} (xᵥ : IsValueᵢ x) →
                  x ≈∙ᵢ [ extractValueᵢ xᵥ ]ᵢ
extract-IsValueᵢ = Eq.extract-IsValueᵢ reflᵢ

extract-IsValue : ∀ {x} (xᵥ : IsValue x) → x ≈∙ [ extractValue xᵥ ]
extract-IsValue xᵥ i = extract-IsValueᵢ (xᵥ i)
