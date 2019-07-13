
open import Relation.Binary using (Rel; Setoid)

module RoutingLib.Data.List.Relation.Binary.Sublist.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Data.List hiding (tail; _∷ʳ_)
open import Data.List.Relation.Binary.Sublist.Setoid S
open import Data.List.Relation.Binary.Equality.Setoid S
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (¬_)
open import RoutingLib.Data.List.Relation.Binary.Equality.Setoid S

infix 4 _⊂_

_⊂_ : Rel (List A) (a ⊔ ℓ)
xs ⊂ ys = xs ⊆ ys × ¬ (xs ≋ ys)

_∷ₛ_ : ∀ {x y xs ys} → x ≈ y → xs ⊂ ys → x ∷ xs ⊂ y ∷ ys
x≈y ∷ₛ (xs⊆ys , ¬xs≋ys) = x≈y ∷ xs⊆ys , ¬xs≋ys ∘ tail

postulate _∷ʳₛ′_ : ∀ y {xs ys} → xs ⊆ ys → xs ⊂ y ∷ ys
-- y ∷ʳₛ′ xs⊆ys = y ∷ʳ xs⊆ys , {!!}

_∷ʳₛ_ : ∀ y {xs ys} → xs ⊂ ys → xs ⊂ y ∷ ys
y ∷ʳₛ (xs⊆ys , ¬xs≋ys) = y ∷ʳₛ′ xs⊆ys

