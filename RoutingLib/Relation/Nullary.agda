open import Data.Fin using (Fin; raise)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_)
open import Function.Bijection using (Bijection; _⤖_)
open import Relation.Binary.PropositionalEquality using (cong; _≡_; refl)

module RoutingLib.Relation.Nullary where

Finite : ∀ {a} (A : Set a) → Set _
Finite A = ∃ λ n → (A ⤖ Fin n)

{-
module _ {a b} {A : Set a} {B : Set b} (finA : Finite A) (finB : Finite B) where

  ∣A∣ : ℕ
  ∣A∣ = proj₁ finA

  ∣B∣ : ℕ
  ∣B∣ = proj₁ finB

  open Bijection (proj₂ finA) renaming (to to toA)
  open Bijection (proj₂ finB) renaming (to to toB)

  ×-finite : Finite (A × B)
  ×-finite = {!!}

  to⊎ : A ⊎ B → Fin (∣A∣ + ∣B∣)
  to⊎ (inj₁ a) = raise {!!} {!!}
  to⊎ (inj₂ b) = {!!}

  from⊎ : Fin (∣A∣ + ∣B∣) → A ⊎ B
  from⊎ i = {!!}

  to⊎-injective : ∀ {x y} → to⊎ x ≡ to⊎ y → x ≡ y
  to⊎-injective = {!!}

  to⊎∘from⊎ : ∀ x → to⊎ (from⊎ x) ≡ x
  to⊎∘from⊎ x = {!!}

  ⊎-finite : Finite (A ⊎ B)
  ⊎-finite = ∣A∣ + ∣B∣ , record
    { to        = record
      { _⟨$⟩_ = to⊎
      ; cong  = cong to⊎
      }
    ; bijective = record
      { injective  = to⊎-injective
      ; surjective = record
        { from             = record
          { _⟨$⟩_ = from⊎
          ; cong  = cong from⊎
          }
        ; right-inverse-of = {!!}
        }
      }
    }
-}
