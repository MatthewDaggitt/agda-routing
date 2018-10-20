open import Algebra.FunctionProperties
open import Relation.Binary using (TotalOrder; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import RoutingLib.Algebra.FunctionProperties
import RoutingLib.Algebra.Selectivity.NaturalChoice.Min.TotalOrder as Min
import RoutingLib.Algebra.Selectivity.NaturalChoice.Max.TotalOrder as Max
open import RoutingLib.Algebra.Selectivity.Lifting
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.TotalOrder as NonStrictToStrict

module RoutingLib.Data.List.Extrema.Core
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

  ------------------------------------------------------------------------------
  -- Setup

  open TotalOrder totalOrder renaming (Carrier to B)
  open NonStrictToStrict totalOrder using (_<_; ≤-<-trans; <-≤-trans)

  open Max totalOrder
  open Min totalOrder



  private

    module _ {a} {A : Set a} (f : A → B) where

      lemma₁ : ∀ {x y v} → f x ≤ v → f x ⊓ f y ≈ f y → f y ≤ v
      lemma₁ fx≤v fx⊓fy≈fy = trans (x⊓y≈y⇒y≤x fx⊓fy≈fy) fx≤v

      lemma₂ : ∀ {x y v} → f y ≤ v → f x ⊓ f y ≈ f x → f x ≤ v
      lemma₂ fy≤v fx⊓fy≈fx = trans (x⊓y≈x⇒x≤y fx⊓fy≈fx) fy≤v

      lemma₃ : ∀ {x y v} → f x < v → f x ⊓ f y ≈ f y → f y < v
      lemma₃ fx<v fx⊓fy≈fy = ≤-<-trans (x⊓y≈y⇒y≤x fx⊓fy≈fy) fx<v

      lemma₄ : ∀ {x y v} → f y < v → f x ⊓ f y ≈ f x → f x < v
      lemma₄ fx<v fx⊓fy≈fy = ≤-<-trans (x⊓y≈x⇒x≤y fx⊓fy≈fy) fx<v



  module _ {a} {A : Set a} where

    ⊓-lift : (A → B) → Op₂ A
    ⊓-lift = Lift _≈_ ⊓-sel

    ⊔-lift : (A → B) → Op₂ A
    ⊔-lift = Lift _≈_ ⊔-sel

    -- Properties

    ⊓-lift-sel : ∀ f → Selective _≡_ (⊓-lift f)
    ⊓-lift-sel f = sel _≈_ ⊓-sel f

    ⊔-lift-sel : ∀ f → Selective _≡_ (⊔-lift f)
    ⊔-lift-sel f = sel _≈_ ⊔-sel f


    ⊓-lift-presᵒ-≤v : ∀ f {v} → (⊓-lift f) Preservesᵒ (λ x → f x ≤ v)
    ⊓-lift-presᵒ-≤v f = presᵒ _≈_ ⊓-sel f (lemma₁ f) (lemma₂ f)

    ⊓-lift-presᵒ-<v : ∀ f {v} → (⊓-lift f) Preservesᵒ (λ x → f x < v)
    ⊓-lift-presᵒ-<v f = presᵒ _≈_ ⊓-sel f (lemma₃ f) (lemma₄ f)

    ⊓-lift-presᵇ-v≤ : ∀ f {v} → (⊓-lift f) Preservesᵇ (λ x → v ≤ f x)
    ⊓-lift-presᵇ-v≤ f {v} = presᵇ _≈_ ⊓-sel f (λ x → v ≤ f x)

    ⊓-lift-presᵇ-v< : ∀ f {v} → (⊓-lift f) Preservesᵇ (λ x → v < f x)
    ⊓-lift-presᵇ-v< f {v} = presᵇ _≈_ ⊓-sel f (λ x → v < f x)

    ⊓-lift-forcesᵇ-v≤ : ∀ f {v} → (⊓-lift f) Forcesᵇ (λ x → v ≤ f x)
    ⊓-lift-forcesᵇ-v≤ f {v} = forcesᵇ _≈_ ⊓-sel f
      (λ v≤fx fx⊓fy≈fx → trans v≤fx (x⊓y≈x⇒x≤y fx⊓fy≈fx))
      (λ v≤fy fx⊓fy≈fy → trans v≤fy (x⊓y≈y⇒y≤x fx⊓fy≈fy))


    ⊔-lift-presᵇ-≤v : ∀ f {v} → ⊔-lift f Preservesᵇ (λ x → f x ≤ v)
    ⊔-lift-presᵇ-≤v f {v} = presᵇ _≈_ ⊔-sel f (λ x → f x ≤ v)

    ⊔-lift-presᵇ-<v : ∀ f {v} → ⊔-lift f Preservesᵇ (λ x → f x < v)
    ⊔-lift-presᵇ-<v f {v} = presᵇ _≈_ ⊔-sel f (λ x → f x < v)

    ⊔-lift-presᵒ-v≤ : ∀ f {v} → ⊔-lift f Preservesᵒ (λ x → v ≤ f x)
    ⊔-lift-presᵒ-v≤ f {v} = presᵒ _≈_ ⊔-sel f
      (λ v≤fx fx⊔fy≈fy → trans v≤fx (x⊔y≈y⇒x≤y fx⊔fy≈fy))
      (λ v≤fy fx⊔fy≈fx → trans v≤fy (x⊔y≈x⇒y≤x fx⊔fy≈fx))

    ⊔-lift-presᵒ-v< : ∀ f {v} → ⊔-lift f Preservesᵒ (λ x → v < f x)
    ⊔-lift-presᵒ-v< f {v} = presᵒ _≈_ ⊔-sel f
      (λ v<fx fx⊔fy≈fy → <-≤-trans v<fx (x⊔y≈y⇒x≤y fx⊔fy≈fy))
      (λ v<fy fx⊔fy≈fx → <-≤-trans v<fy (x⊔y≈x⇒y≤x fx⊔fy≈fx))

    ⊔-lift-forcesᵇ-≤v : ∀ f {v} → (⊔-lift f) Forcesᵇ (λ x → f x ≤ v)
    ⊔-lift-forcesᵇ-≤v f {v} = forcesᵇ _≈_ ⊔-sel f
      (λ fx≤v fx⊔fy≈fx → trans (x⊔y≈x⇒y≤x fx⊔fy≈fx) fx≤v)
      (λ fy≤v fx⊔fy≈fy → trans (x⊔y≈y⇒x≤y fx⊔fy≈fy) fy≤v)
