open import Algebra.FunctionProperties
open import Relation.Binary using (TotalOrder; Setoid)
import Relation.Binary.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.PropositionalEquality using (_≡_)

open import RoutingLib.Algebra.FunctionProperties
import RoutingLib.Algebra.Selectivity.NaturalChoice.Min.TotalOrder as Min
import RoutingLib.Algebra.Selectivity.NaturalChoice.Max.TotalOrder as Max
open import RoutingLib.Algebra.Selectivity.Lifting

module RoutingLib.Data.List.Extrema.Core
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

  ------------------------------------------------------------------------------
  -- Setup
  
  
  open TotalOrder totalOrder renaming (Carrier to B)
  open NonStrictToStrict _≈_ _≤_ using (_<_)
   
  open Max totalOrder
  open Min totalOrder

  module _ {a} {A : Set a} where
  
    ⊓-lift : (A → B) → Op₂ A
    ⊓-lift = Lift _≈_ ⊓-sel

    ⊔-lift : (A → B) → Op₂ A
    ⊔-lift = Lift _≈_ ⊔-sel
    
    -- Properties

    lemma₁ : ∀ (f : A → B) {x y v} → f x ≤ v → f x ⊓ f y ≈ f y → f y ≤ v
    lemma₁ _ fx≤v fx⊓fy≈fy = trans (x⊓y≈y⇒y≤x fx⊓fy≈fy) fx≤v

    lemma₂ : ∀ (f : A → B) {x y v} → f y ≤ v → f x ⊓ f y ≈ f x → f x ≤ v
    lemma₂ _ fy≤v fx⊓fy≈fx = trans (x⊓y≈x⇒x≤y fx⊓fy≈fx) fy≤v
    
    lemma₃ : ∀ (f : A → B) {x y v} → f x < v → f x ⊓ f y ≈ f y → f y < v
    lemma₃ _ fx<v fx⊓fy≈fy = {!!}

    lemma₄ : ∀ (f : A → B) {x y v} → f y < v → f x ⊓ f y ≈ f x → f x < v
    lemma₄ _ fx<v fx⊓fy≈fy = {!!}


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
