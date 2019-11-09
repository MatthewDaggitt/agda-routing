open import Data.Product using (proj₁; proj₂)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (¬_)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict

open import RoutingLib.Relation.Binary
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict′

module RoutingLib.Relation.Binary.Construct.NonStrictToStrict.PartialOrder
  {a ℓ₁ ℓ₂} (poset : Poset a ℓ₁ ℓ₂) where

  open Poset poset
  open NonStrictToStrict _≈_ _≤_ using (_<_; <⇒≤; <⇒≉; ≤∧≉⇒<) public

  <-strictPartialOrder : StrictPartialOrder a ℓ₁ _
  <-strictPartialOrder = record
    { isStrictPartialOrder =
      NonStrictToStrict.<-isStrictPartialOrder
        _≈_ _≤_ isPartialOrder
    }

  open StrictPartialOrder <-strictPartialOrder public
    using (<-resp-≈)
    renaming
    ( irrefl     to <-irrefl
    ; trans      to <-trans
    ; asymmetric to <-asym
    ; isStrictPartialOrder to <-isStrictPartialOrder
    )

  <-≤-trans : ∀ {x y z} → x < y → y ≤ z → x < z
  <-≤-trans = NonStrictToStrict.<-≤-trans _ _≤_ Eq.sym trans antisym (proj₁ ≤-resp-≈)

  ≤-<-trans : ∀ {x y z} → x ≤ y → y < z → x < z
  ≤-<-trans = NonStrictToStrict.≤-<-trans _ _≤_ trans antisym (proj₂ ≤-resp-≈)

  <⇒≱ : ∀ {x y} → x < y → ¬ (y ≤ x)
  <⇒≱ = NonStrictToStrict.<⇒≱ _ _≤_ antisym

  ≤⇒≯ : ∀ {x y} → x ≤ y → ¬ (y < x)
  ≤⇒≯ = NonStrictToStrict.≤⇒≯ _ _≤_ antisym

  <-respˡ-≈ : _<_ Respectsˡ _≈_
  <-respˡ-≈ = NonStrictToStrict.<-respˡ-≈ _ _≤_ Eq.trans (proj₂ ≤-resp-≈)

  <-respʳ-≈ : _<_ Respectsʳ _≈_
  <-respʳ-≈ = NonStrictToStrict.<-respʳ-≈ _ _≤_ Eq.sym Eq.trans (proj₁ ≤-resp-≈)
