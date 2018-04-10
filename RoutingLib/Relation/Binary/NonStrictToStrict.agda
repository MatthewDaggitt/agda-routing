open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)


module RoutingLib.Relation.Binary.NonStrictToStrict
  {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂)
  where

  open import Relation.Binary.NonStrictToStrict _≈_ _≤_

  <⇒≱ : Antisymmetric _≈_ _≤_ → ∀ {x y} → x < y → ¬ (y ≤ x)
  <⇒≱ antisym (x≤y , x≉y) y≤x = x≉y (antisym x≤y y≤x)

  ≤⇒≯ : Antisymmetric _≈_ _≤_ → ∀ {x y} → x ≤ y → ¬ (y < x)
  ≤⇒≯ antisym x≤y y<x = <⇒≱ antisym y<x x≤y

  ≰⇒> : Symmetric _≈_ → _≈_ ⇒ _≤_ → Total _≤_ →
        ∀ {x y} → ¬ (x ≤ y) → y < x
  ≰⇒> sym refl total {x} {y} x≰y with total x y
  ... | inj₁ x≤y = contradiction x≤y x≰y
  ... | inj₂ y≤x = y≤x , x≰y ∘ refl ∘ sym

  postulate ≮⇒≥ : ∀ {x y} → ¬ (x < y) → y ≤ x
  
  <≤-trans : Symmetric _≈_ → Transitive _≤_ → Antisymmetric _≈_ _≤_ →
             (∀ {x} → (x ≤_) Respects _≈_) →
             ∀ {x y z} → x < y → y ≤ z → x < z
  <≤-trans sym trans antisym respʳ (x≤y , x≉y) y≤z =
    trans x≤y y≤z , (λ x≈z → x≉y (antisym x≤y (respʳ (sym x≈z) y≤z )))

  ≤<-trans : Transitive _≤_ → Antisymmetric _≈_ _≤_ →
             (∀ {x} → (_≤ x) Respects _≈_) →
             ∀ {x y z} → x ≤ y → y < z → x < z
  ≤<-trans trans antisym respʳ x≤y (y≤z , y≉z) =
    trans x≤y y≤z , (λ x≈z → y≉z (antisym y≤z (respʳ x≈z x≤y)))
