open import Data.Bool
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (contradiction)

module RoutingLib.Data.Bool where

  data _<_ : Rel Bool ℓ₀ where
    f<t : false < true

  <-trans : Transitive _<_
  <-trans f<t ()

  <-cmp : Trichotomous _≡_ _<_
  <-cmp false false = tri≈ (λ ()) refl (λ ())
  <-cmp false true  = tri< f<t (λ ()) (λ ())
  <-cmp true  false = tri> (λ ()) (λ ()) f<t
  <-cmp true  true  = tri≈ (λ ()) refl (λ ())

  <-minimum : ∀ {x} → x ≢ false → false < x
  <-minimum {false} neq = contradiction refl neq
  <-minimum {true}  _   = f<t
  
  <-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
  <-isStrictTotalOrder = record
    { isEquivalence = isEquivalence
    ; trans         = <-trans
    ; compare       = <-cmp
    }
