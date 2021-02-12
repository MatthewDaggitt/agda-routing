open import Level using (_⊔_)
open import Algebra.Core
open import Algebra.Definitions
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Construct.Add.Point using (Pointed; ∙; [_])
import Relation.Binary.Construct.Add.Point.Equality as PointedEquality
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_)

open import RoutingLib.Algebra.Definitions

module RoutingLib.Algebra.Construct.Add.Zero {a} {A : Set a} (_⊕_ : Op₂ A) where

A∙ : Set a
A∙ = Maybe A

infix 6 _⊕∙_

_⊕∙_ : Op₂ A∙
∙     ⊕∙ v       = ∙
v     ⊕∙ ∙ = ∙
[ v ] ⊕∙ [ w ]  = [ v ⊕ w ]

module _ {ℓ} {_≈_ : Rel A ℓ} (refl : Reflexive _≈_) where

  open PointedEquality _≈_

  ⊕∙-comm : Commutative _≈_ _⊕_ → Commutative _≈∙_ _⊕∙_
  ⊕∙-comm comm ∙       ∙       = ∙≈∙
  ⊕∙-comm comm [ v ] ∙       = ∙≈∙
  ⊕∙-comm comm ∙     [ w ] = ∙≈∙
  ⊕∙-comm comm [ v ] [ w ] = [ comm v w ]

  ⊕∙-sel : Selective _≈_ _⊕_ → Selective _≈∙_ _⊕∙_
  ⊕∙-sel sel ∙       ∙       = inj₁ ∙≈∙
  ⊕∙-sel sel [ v ] ∙       = inj₂ ∙≈∙
  ⊕∙-sel sel ∙       [ w ] = inj₁ ∙≈∙
  ⊕∙-sel sel [ v ] [ w ] with sel v w
  ... | inj₁ v⊕w≈v = inj₁ [ v⊕w≈v ]
  ... | inj₂ v⊕w≈w = inj₂ [ v⊕w≈w ]

  ⊕∙-assoc : Associative _≈_ _⊕_ → Associative _≈∙_ _⊕∙_
  ⊕∙-assoc assoc ∙     ∙     ∙     = ∙≈∙
  ⊕∙-assoc assoc ∙     ∙     [ w ] = ∙≈∙
  ⊕∙-assoc assoc ∙     [ v ] ∙     = ∙≈∙
  ⊕∙-assoc assoc ∙     [ v ] [ w ] = ∙≈∙
  ⊕∙-assoc assoc [ u ] ∙     ∙     = ∙≈∙
  ⊕∙-assoc assoc [ u ] ∙     [ w ] = ∙≈∙
  ⊕∙-assoc assoc [ u ] [ v ] ∙     = ∙≈∙
  ⊕∙-assoc assoc [ u ] [ v ] [ w ] = [ assoc u v w ]

  ⊕∙-zeroˡ : LeftZero _≈∙_ ∙ _⊕∙_
  ⊕∙-zeroˡ ∙     = ∙≈∙
  ⊕∙-zeroˡ [ v ] = ∙≈∙

  ⊕∙-zeroʳ : RightZero _≈∙_ ∙ _⊕∙_
  ⊕∙-zeroʳ ∙     = ∙≈∙
  ⊕∙-zeroʳ [ v ] = ∙≈∙

  ⊕∙-zero : Zero _≈∙_ ∙ _⊕∙_
  ⊕∙-zero = ⊕∙-zeroˡ , ⊕∙-zeroʳ

  ⊕∙-pres-≈∙ : Congruent₂ _≈_ _⊕_ → Congruent₂ _≈∙_ _⊕∙_
  ⊕∙-pres-≈∙ _    ∙≈∙    ∙≈∙    = ∙≈∙
  ⊕∙-pres-≈∙ _    ∙≈∙    [ w≈x ] = ∙≈∙
  ⊕∙-pres-≈∙ _    [ u≈v ] ∙≈∙             = ∙≈∙
  ⊕∙-pres-≈∙ pres [ u≈v ] [ w≈x ] = [ pres u≈v w≈x ]
