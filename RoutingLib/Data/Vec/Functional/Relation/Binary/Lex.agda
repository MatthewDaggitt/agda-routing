

open import Relation.Binary

module RoutingLib.Data.Vec.Functional.Relation.Binary.Lex
  {a ℓ₁ ℓ₂} {A : Set a} (P : Set) (_≈_ : Rel A ℓ₁) (_∼_ : Rel A ℓ₂)
  where

open import Level using (_⊔_)
open import Data.Nat hiding (_⊔_)
open import Data.Vec.Functional
    
data Lex : {n : ℕ} → Rel (Vector A n) (a ⊔ ℓ₁ ⊔ ℓ₂) where
  base : P                                                                → Lex []       []
  this : ∀ {x y n} {xs ys : Vector A n} (x∼y : x ∼ y)                     → Lex (x ∷ xs) (y ∷ ys)
  next : ∀ {x y n} {xs ys : Vector A n} (x≈y : x ≈ y) (xs<ys : Lex xs ys) → Lex (x ∷ xs) (y ∷ ys)

