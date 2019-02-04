open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Level as Level using (lift)
open import Relation.Unary using (_∈_)
open import Relation.Binary.Indexed.Homogeneous hiding (Lift)

open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.Add.Point.Equality
  renaming (_≈∙ᵢ_ to BLift)
open import RoutingLib.Relation.Nullary.Indexed.Construct.Add.Point

module RoutingLib.Relation.Unary.Indexed.Construct.Add.Point.Exclude
  {a i} {I : Set i} {Aᵢ : I → Set a}  where

private
  A∙ᵢ : I → Set a
  A∙ᵢ = Pointedᵢ Aᵢ

Lift∙ : ∀ {p} → IPred Aᵢ p → IPred (Pointedᵢ Aᵢ) p
Lift∙ {_} Pᵢ i [ xᵢ ]ᵢ = Pᵢ i xᵢ
Lift∙ {p} Pᵢ i ∙ᵢ     = Level.Lift p ⊥

------------------------------------------------------------------------
-- Properties

module _ {p} {Pᵢ : IPred Aᵢ p} where

  ∈-isValueᵢ : ∀ {i} {xᵢ : A∙ᵢ i} → xᵢ ∈ Lift∙ Pᵢ i → IsValueᵢ xᵢ
  ∈-isValueᵢ {i} {[ xᵢ ]ᵢ} x∈P = [ tt ]ᵢ
  ∈-isValueᵢ {i} {∙ᵢ}     ()

  ∈-isValue : ∀ {x} → x ∈ᵢ Lift∙ Pᵢ → IsValue x
  ∈-isValue x∈P i = ∈-isValueᵢ (x∈P i)

  ∈-extractValueᵢ : ∀ {i} {xᵢ : A∙ᵢ i} (xᵥ : IsValueᵢ xᵢ) →
                    xᵢ ∈ Lift∙ Pᵢ i → extractValueᵢ xᵥ ∈ Pᵢ i
  ∈-extractValueᵢ [ xᵢ ]ᵢ x∈P = x∈P

  ∈-extractValue : ∀ {x} (xᵥ : IsValue x) →
                   x ∈ᵢ Lift∙ Pᵢ → extractValue xᵥ ∈ᵢ Pᵢ
  ∈-extractValue xᵥ x∈P i = ∈-extractValueᵢ (xᵥ i) (x∈P i)

  Lift∙-congᵢ : ∀ {ℓ} {_≈ᵢ_ : IRel Aᵢ ℓ} →
              (∀ {i} {xᵢ yᵢ} → xᵢ ≈ᵢ yᵢ → xᵢ ∈ Pᵢ i → yᵢ ∈ Pᵢ i) →
              (∀ {i} {xᵢ yᵢ} → BLift Aᵢ _≈ᵢ_ xᵢ yᵢ → xᵢ ∈ Lift∙ Pᵢ i → yᵢ ∈ Lift∙ Pᵢ i)
  Lift∙-congᵢ Pᵢ-cong ∙≈ᵢ∙ (lift ())
  Lift∙-congᵢ Pᵢ-cong [ xᵢ ]ᵢ x∈Pᵢ = Pᵢ-cong xᵢ x∈Pᵢ

  Lift∙-cong : ∀ {ℓ} {_≈ᵢ_ : IRel Aᵢ ℓ} →
              (∀ {i} {xᵢ yᵢ} → xᵢ ≈ᵢ yᵢ → xᵢ ∈ Pᵢ i → yᵢ ∈ Pᵢ i) →
              (∀ {x y} → (∀ i → BLift Aᵢ _≈ᵢ_ (x i) (y i)) → x ∈ᵢ Lift∙ Pᵢ → y ∈ᵢ Lift∙ Pᵢ)
  Lift∙-cong Pᵢ-cong x≈y x∈Pᵢ i = Lift∙-congᵢ Pᵢ-cong (x≈y i) (x∈Pᵢ i)
