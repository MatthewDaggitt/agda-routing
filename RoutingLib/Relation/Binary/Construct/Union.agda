
module RoutingLib.Relation.Binary.Construct.Union where

open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Product
open import Level
open import Relation.Binary
open import Relation.Binary.Construct.Union

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b

-- Note: Change names in respects in Relation.Binary

module _ {≈ : Rel A ℓ₁} (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  respˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∪ R) Respectsˡ ≈
  respˡ Lˡ Rˡ x≈y = Sum.map (Lˡ x≈y) (Rˡ x≈y)

module _ {≈ : Rel B ℓ₁} (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  respʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∪ R) Respectsʳ ≈
  respʳ Lʳ Rʳ x≈y = Sum.map (Lʳ x≈y) (Rʳ x≈y)

module _ {≈ : Rel A ℓ₁} {L : Rel A ℓ₂} {R : Rel A ℓ₃} where

  resp₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∪ R) Respects₂ ≈
  resp₂ (Lʳ , Lˡ) (Rʳ , Rˡ) = respʳ L R Lʳ Rʳ , respˡ L R Lˡ Rˡ
