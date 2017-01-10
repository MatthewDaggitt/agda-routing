open import Relation.Binary
open import Data.Product
open import Data.Sum

open import Relation.Binary.Product.StrictLex hiding (×-total)

module RoutingLib.Relation.Binary.Product.StrictLex {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where
  
  -- An alternative version of the theorem in the stdlib
  ×-total₂ : ∀ {_≈₁_ _<₁_ : Rel A₁ ℓ₁} →
            Symmetric _≈₁_ → Trichotomous _≈₁_ _<₁_ → 
            {_≤₂_ : Rel A₂ ℓ₂} → Total _≤₂_ →
            Total (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-total₂ sym tri₁ total₂ x y with tri₁ (proj₁ x) (proj₁ y)
  ... | tri< x₁<y₁ _ _ = inj₁ (inj₁ x₁<y₁)
  ... | tri> _ _ y₁<x₁ = inj₂ (inj₁ y₁<x₁)
  ... | tri≈ _ x₁≈y₁ _ with total₂ (proj₂ x) (proj₂ y)
  ...   | inj₁ x₂≤y₂ = inj₁ (inj₂ (x₁≈y₁     , x₂≤y₂))
  ...   | inj₂ y₂≤x₂ = inj₂ (inj₂ (sym x₁≈y₁ , y₂≤x₂))
