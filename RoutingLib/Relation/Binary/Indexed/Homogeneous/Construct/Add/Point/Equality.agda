open import Level
open import Relation.Binary using (Rel)
open import Relation.Binary.Indexed.Homogeneous hiding (Rel)
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec

open import RoutingLib.Relation.Nullary.Indexed.Construct.Add.Point

module RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.Add.Point.Equality
  {i a ℓ} {I : Set i} (Aᵢ : I → Set a) (_≈ᵢ_ : IRel Aᵢ ℓ) where

data _≈∙ᵢ_ : IRel (Pointedᵢ Aᵢ) (a ⊔ i ⊔ ℓ) where
  ∙≈ᵢ∙ : ∀ {i} → _≈∙ᵢ_ {i} ∙ᵢ ∙ᵢ
  [_]ᵢ : ∀ {i} {k l : Aᵢ i} → k ≈ᵢ l → [ k ]ᵢ ≈∙ᵢ [ l ]ᵢ

[_]≈ : ∀ {x y : ∀ i → Aᵢ i} → (∀ i → x i ≈ᵢ y i) →
         (∀ i → [ x ] i ≈∙ᵢ [ y ] i)
[ x≈y ]≈ i = [ x≈y i ]ᵢ

[≈]ᵢ-injective : ∀ {i} {k l : Aᵢ i} → [ k ]ᵢ ≈∙ᵢ [ l ]ᵢ → k ≈ᵢ l
[≈]ᵢ-injective [ k≈l ]ᵢ = k≈l

[≈]-injective : ∀ {k l : ∀ i → Aᵢ i} → (∀ i → [ k ] i ≈∙ᵢ [ l ] i) → (∀ i → k i ≈ᵢ l i)
[≈]-injective k≈l i = [≈]ᵢ-injective (k≈l i)

≈∙ᵢ-refl : Reflexive Aᵢ _≈ᵢ_ → Reflexive (Pointedᵢ Aᵢ) _≈∙ᵢ_
≈∙ᵢ-refl ≈-refl {_} {∙ᵢ}     = ∙≈ᵢ∙
≈∙ᵢ-refl ≈-refl {_} {[ k ]ᵢ} = [ ≈-refl ]ᵢ

≈∙ᵢ-sym : Symmetric Aᵢ _≈ᵢ_ → Symmetric (Pointedᵢ Aᵢ) _≈∙ᵢ_
≈∙ᵢ-sym ≈-sym ∙≈ᵢ∙     = ∙≈ᵢ∙
≈∙ᵢ-sym ≈-sym [ x≈y ]ᵢ = [ ≈-sym x≈y ]ᵢ

≈∙ᵢ-trans : Transitive Aᵢ _≈ᵢ_ → Transitive (Pointedᵢ Aᵢ) _≈∙ᵢ_
≈∙ᵢ-trans ≈-trans ∙≈ᵢ∙     ∙≈z     = ∙≈z
≈∙ᵢ-trans ≈-trans [ x≈y ]ᵢ [ y≈z ]ᵢ = [ ≈-trans x≈y y≈z ]ᵢ

≈∙ᵢ-dec : Decidable Aᵢ _≈ᵢ_ → Decidable (Pointedᵢ Aᵢ) _≈∙ᵢ_
≈∙ᵢ-dec _≟_ ∙ᵢ     ∙ᵢ     = yes ∙≈ᵢ∙
≈∙ᵢ-dec _≟_ ∙ᵢ     [ l ]ᵢ = no (λ ())
≈∙ᵢ-dec _≟_ [ k ]ᵢ ∙ᵢ     = no (λ ())
≈∙ᵢ-dec _≟_ [ k ]ᵢ [ l ]ᵢ = Dec.map′ [_]ᵢ [≈]ᵢ-injective (k ≟ l)

{-
≈∙-irrelevant : Irrelevant Aᵢ _≈ᵢ_ → Irrelevant _≈∙ᵢ_
≈∙-irrelevant ≈-irr ∙≈∙   ∙≈∙   = P.refl
≈∙-irrelevant ≈-irr [ p ] [ q ] = P.cong _ (≈-irr p q)

≈∙-substitutive : ∀ {ℓ} → Substitutive Aᵢ _≈ᵢ_ ℓ → Substitutive _≈∙_ ℓ
≈∙-substitutive ≈-subst P ∙≈∙   = id
≈∙-substitutive ≈-subst P [ p ] = ≈-subst (P ∘′ [_]) p
-}

------------------------------------------------------------------------
-- Structures

≈∙ᵢ-isIEquivalence : IsIndexedEquivalence Aᵢ _≈ᵢ_ →
                     IsIndexedEquivalence (Pointedᵢ Aᵢ) _≈∙ᵢ_
≈∙ᵢ-isIEquivalence ≈-isEquivalence = record
  { reflᵢ  = ≈∙ᵢ-refl reflᵢ
  ; symᵢ   = ≈∙ᵢ-sym symᵢ
  ; transᵢ = ≈∙ᵢ-trans transᵢ
  } where open IsIndexedEquivalence ≈-isEquivalence

≈∙ᵢ-isIDecEquivalence : IsIndexedDecEquivalence Aᵢ _≈ᵢ_ →
                        IsIndexedDecEquivalence (Pointedᵢ Aᵢ) _≈∙ᵢ_
≈∙ᵢ-isIDecEquivalence ≈-isDecEquivalence = record
  { isEquivalenceᵢ = ≈∙ᵢ-isIEquivalence isEquivalenceᵢ
  ; _≟ᵢ_           = ≈∙ᵢ-dec _≟ᵢ_
  } where open IsIndexedDecEquivalence ≈-isDecEquivalence

------------------------------------------------------------------------
-- Other properties

private
  _≈_ : Rel (∀ i → Aᵢ i) (i ⊔ ℓ)
  x ≈ y = ∀ i → x i ≈ᵢ y i

  _≈∙_ : Rel (∀ i → Pointedᵢ Aᵢ i) (i ⊔ a ⊔ ℓ)
  x ≈∙ y = ∀ i → x i ≈∙ᵢ y i

extractValueᵢ-cong : ∀ {i} {x y : Pointedᵢ Aᵢ i} → x ≈∙ᵢ y →
                    (xᵥ : IsValueᵢ x) (yᵥ : IsValueᵢ y) →
                    extractValueᵢ xᵥ ≈ᵢ extractValueᵢ yᵥ
extractValueᵢ-cong [ x≈y ]ᵢ [ x ]ᵢ [ y ]ᵢ = x≈y

extractValue-cong : ∀ {x y : (∀ i → Pointedᵢ Aᵢ i)} → (∀ i → x i ≈∙ᵢ y i) →
                    (xᵥ : IsValue x) (yᵥ : IsValue y) →
                    extractValue xᵥ ≈ extractValue yᵥ
extractValue-cong x≈y xᵥ yᵥ i = extractValueᵢ-cong (x≈y i) (xᵥ i) (yᵥ i)

IsValueᵢ-resp-≈∙ : ∀ {i} {x y : Pointedᵢ Aᵢ i} →
                   x ≈∙ᵢ y → IsValueᵢ x → IsValueᵢ y
IsValueᵢ-resp-≈∙ [ _ ]ᵢ [ x ]ᵢ = [ x ]ᵢ

IsValue-resp-≈∙ : ∀ {x y} → x ≈∙ y → IsValue x → IsValue y
IsValue-resp-≈∙ x≈y xᵥ i = IsValueᵢ-resp-≈∙ (x≈y i) (xᵥ i)

extract-IsValueᵢ : Reflexive Aᵢ _≈ᵢ_ →
                  ∀ {i} {x : Pointedᵢ Aᵢ i} (xᵥ : IsValueᵢ x) →
                  x ≈∙ᵢ [ extractValueᵢ xᵥ ]ᵢ
extract-IsValueᵢ refl [ x ]ᵢ = [ refl ]ᵢ
