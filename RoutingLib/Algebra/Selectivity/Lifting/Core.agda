open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Rel)

module RoutingLib.Algebra.Selectivity.Lifting.Core where


  Lift : ∀ {a b ℓ} {A : Set a} {B : Set b} (_≈_ : Rel A ℓ)
           (_⊕_ : Op₂ A) → Selective _≈_ _⊕_ → (B → A) → Op₂ B
  Lift _ _ ⊕-sel f x y with ⊕-sel (f x) (f y)
  ... | inj₁ _ = x
  ... | inj₂ _ = y
