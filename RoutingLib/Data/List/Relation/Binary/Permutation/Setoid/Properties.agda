open import Data.List
open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc)
open import Relation.Unary using (Decidable; Pred)
open import Relation.Binary
  using (Setoid; Rel; Reflexive; Transitive; Symmetric; IsEquivalence; _Respects_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

import Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid

module RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties
  {b} {ℓ} (S : Setoid b ℓ)  where

open PermutationSetoid S
open Setoid S using (_≈_; sym) renaming (Carrier to A)

-------------------

module _ {p} {P : Pred A p} (P? : Decidable P) (P≈ : P Respects _≈_) where

  filter⁺ : ∀ {xs ys : List A} → xs ↭ ys → filter P? xs ↭ filter P? ys
  filter⁺ refl = refl
  filter⁺ (trans xs↭zs zs↭ys) = trans (filter⁺ xs↭zs) (filter⁺ zs↭ys)
  filter⁺ {x ∷ xs} {y ∷ ys} (prep x=x' A=A') with P? x | P? y
  ... | yes Px | yes Px' = prep x=x' (filter⁺ A=A')
  ... | yes Px | no ¬Px' = contradiction (P≈ x=x' Px) ¬Px'
  ... | no ¬Px | yes Px' = contradiction (P≈ (sym x=x') Px') ¬Px
  ... | no ¬Px | no ¬Px' = filter⁺ A=A'
  filter⁺ {x ∷ y ∷ A} {y' ∷ x' ∷ A'} (swap x=x' y=y' A=A') with P? x | P? y'
  ... | no ¬Px | no ¬Py' = prf
    where
    prf : filter P? (y ∷ A) ↭ filter P? (x' ∷ A')
    prf with P? x' | P? y
    ... | no ¬Px' | no ¬Py = filter⁺ A=A'
    ... | no ¬Px' | yes Py = contradiction (P≈ y=y' Py) ¬Py'
    ... | yes Px' | _      = contradiction (P≈ (sym x=x') Px') ¬Px
  ... | no ¬Px | yes Py' = prf
    where
    prf : filter P? (y ∷ A) ↭ y' ∷ filter P? (x' ∷ A')
    prf with
          P? x'   | P? y
    ... | no ¬Px' | no ¬Py = contradiction (P≈ (sym y=y') Py') ¬Py
    ... | no ¬Px' | yes Py = prep y=y' (filter⁺ A=A')
    ... | yes Px' | _      = contradiction (P≈ (sym x=x') Px') ¬Px
  ... | yes Px | no ¬Py' = prf
    where
    prf : x ∷ filter P? (y ∷ A) ↭ filter P? (x' ∷ A')
    prf with P? x' | P? y
    ... | no ¬Px' | _      = contradiction (P≈ x=x' Px) ¬Px'
    ... | yes Px' | no ¬Py = prep x=x' (filter⁺ A=A')
    ... | yes Px' | yes Py = contradiction (P≈ y=y' Py) ¬Py'
  ... | yes Px | yes Py' = prf
    where
    prf : x ∷ filter P? (y ∷ A) ↭ y' ∷ filter P? (x' ∷ A')
    prf with P? x' | P? y
    ... | no ¬Px' | _      = contradiction (P≈ x=x' Px) ¬Px'
    ... | yes Px' | no ¬Py = contradiction (P≈ (sym y=y') Py') ¬Py
    ... | yes Px' | yes Py = swap x=x' y=y' (filter⁺ A=A')

tabulate⁺ : ∀ {n} {f g : Fin n → A} →
            (∀ {i} → f i ≈ g i) → tabulate f ↭ tabulate g
tabulate⁺ {zero}  {f} {g} f=g = refl
tabulate⁺ {suc k} {f} {g} f=g = prep f=g (tabulate⁺ {k} f=g)
