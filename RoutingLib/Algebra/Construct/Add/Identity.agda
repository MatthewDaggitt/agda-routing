
open import Algebra.FunctionProperties.Core using (Op₂)

module RoutingLib.Algebra.Construct.Add.Identity {a} {A : Set a} (_⊕_ : Op₂ A) where

open import Level using (_⊔_)
open import Algebra.FunctionProperties hiding (Op₂)
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (inj₁; inj₂; map)
open import Data.Maybe using (Maybe; Eq; decSetoid; drop-just)
open import Data.Product using (_,_)

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Relation.Nullary.Construct.Add.Point using (Pointed; ∙; [_])
import RoutingLib.Relation.Binary.Construct.Add.Point.Equality as PointedEquality

_⊕∙_ : Op₂ (Pointed A)
∙      ⊕∙ y     = y
x      ⊕∙ ∙     = x
[ x ]  ⊕∙ [ y ] = [ x ⊕ y ]

module _ {ℓ} {_≈_ : Rel A ℓ} (refl : Reflexive _≈_) where

  open PointedEquality _≈_
  
  ⊕∙-comm : Commutative _≈_ _⊕_ → Commutative _≈∙_ _⊕∙_
  ⊕∙-comm comm ∙     ∙     = ∙≈∙
  ⊕∙-comm comm [ _ ] ∙     = [ refl ]
  ⊕∙-comm comm ∙     [ _ ] = [ refl ]
  ⊕∙-comm comm [ x ] [ y ] = [ comm x y ]

  ⊕∙-sel : Selective _≈_ _⊕_ → Selective _≈∙_ _⊕∙_
  ⊕∙-sel sel ∙     ∙     = inj₁ ∙≈∙
  ⊕∙-sel sel [ _ ] ∙     = inj₁ [ refl ]
  ⊕∙-sel sel ∙     [ _ ] = inj₂ [ refl ]
  ⊕∙-sel sel [ x ] [ y ] = map [_] [_] (sel x y)

  ⊕∙-assoc : Associative _≈_ _⊕_ → Associative _≈∙_ _⊕∙_
  ⊕∙-assoc assoc ∙     ∙     ∙     = ∙≈∙
  ⊕∙-assoc assoc ∙     ∙     [ _ ] = [ refl ]
  ⊕∙-assoc assoc ∙     [ _ ] ∙     = [ refl ]
  ⊕∙-assoc assoc ∙     [ _ ] [ _ ] = [ refl ]
  ⊕∙-assoc assoc [ _ ] ∙     ∙     = [ refl ]
  ⊕∙-assoc assoc [ _ ] ∙     [ _ ] = [ refl ]
  ⊕∙-assoc assoc [ _ ] [ _ ] ∙     = [ refl ]
  ⊕∙-assoc assoc [ x ] [ y ] [ z ] = [ assoc x y z ]

  ⊕∙-identityˡ : LeftIdentity _≈∙_ ∙ _⊕∙_
  ⊕∙-identityˡ ∙     = ∙≈∙
  ⊕∙-identityˡ [ _ ] = [ refl ]

  ⊕∙-identityʳ : RightIdentity _≈∙_ ∙ _⊕∙_
  ⊕∙-identityʳ ∙     = ∙≈∙
  ⊕∙-identityʳ [ _ ] = [ refl ]

  ⊕∙-identity : Identity _≈∙_ ∙ _⊕∙_
  ⊕∙-identity = ⊕∙-identityˡ , ⊕∙-identityʳ

  ⊕∙-zeroˡ : ∀ {0#} → LeftZero _≈_ 0# _⊕_ → LeftZero _≈∙_ [ 0# ] _⊕∙_
  ⊕∙-zeroˡ zeroˡ ∙     = [ refl ]
  ⊕∙-zeroˡ zeroˡ [ x ] = [ zeroˡ x ]

  ⊕∙-zeroʳ : ∀ {0#} → RightZero _≈_ 0# _⊕_ → RightZero _≈∙_ [ 0# ] _⊕∙_
  ⊕∙-zeroʳ zeroʳ ∙     = [ refl ]
  ⊕∙-zeroʳ zeroʳ [ x ] = [ zeroʳ x ]

  ⊕∙-zero : ∀ {0#} → Zero _≈_ 0# _⊕_ → Zero _≈∙_ [ 0# ] _⊕∙_
  ⊕∙-zero (zeroˡ , zeroʳ) = ⊕∙-zeroˡ zeroˡ , ⊕∙-zeroʳ zeroʳ

  ⊕∙-cong : Congruent₂ _≈_ _⊕_ → Congruent₂ _≈∙_ _⊕∙_
  ⊕∙-cong cong ∙≈∙     ∙≈∙     = ∙≈∙
  ⊕∙-cong cong ∙≈∙     [ y≈z ] = [ y≈z ]
  ⊕∙-cong cong [ w≈x ] ∙≈∙     = [ w≈x ]
  ⊕∙-cong cong [ w≈x ] [ y≈z ] = [ cong w≈x y≈z ]

