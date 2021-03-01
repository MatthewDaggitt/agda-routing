
open import Data.List hiding (tail; _∷ʳ_)
open import Data.List.Relation.Binary.Pointwise using (tail)
open import Data.Nat using (_≤_; s≤s; _<_)
open import Data.Nat.Properties using (<⇒≢)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (Pred; Decidable)

open import RoutingLib.Function.Reasoning

module RoutingLib.Data.List.Relation.Binary.Sublist.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Data.List.Relation.Binary.Sublist.Setoid S
open import Data.List.Relation.Binary.Sublist.Setoid.Properties S using (length-mono-≤)
open import Data.List.Relation.Binary.Equality.Setoid S

_∷ₛ_ : ∀ {x y xs ys} → x ≈ y → xs ⊂ ys → x ∷ xs ⊂ y ∷ ys
x≈y ∷ₛ (xs⊆ys , ¬xs≋ys) = x≈y ∷ xs⊆ys , ¬xs≋ys ∘ tail

∷ʳ⇒≠ : ∀ y {xs ys} → xs ⊆ ys → ¬ (xs ≋ y ∷ ys)
∷ʳ⇒≠ y {xs} {ys} xs⊆ys = begin⟨ xs⊆ys ⟩
  ∴ xs ⊆ ys                     $⟨ length-mono-≤ ⟩
  ∴ length xs ≤ length ys       $⟨ s≤s ⟩
  ∴ length xs < length (y ∷ ys) $⟨ <⇒≢ ⟩
  ∴ length xs ≢ length (y ∷ ys) $⟨ contraposition ≋-length ⟩
  ∴ ¬ (xs ≋ y ∷ ys)             ∎

_∷ʳₛ′_ : ∀ y {xs ys} → xs ⊆ ys → xs ⊂ y ∷ ys
y ∷ʳₛ′ xs⊆ys = (y ∷ʳ xs⊆ys) , (∷ʳ⇒≠ y xs⊆ys)

_∷ʳₛ_ : ∀ y {xs ys} → xs ⊂ ys → xs ⊂ y ∷ ys
y ∷ʳₛ (xs⊆ys , ¬xs≋ys) = y ∷ʳₛ′ xs⊆ys

