open import Data.Fin using (Fin; raise)
import Data.Fin.Properties as Fin
import Data.List.Membership.Setoid as SetoidMembership
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_)
open import Function
open import Level
open import Relation.Binary as B hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; setoid)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary
open import Relation.Nullary.Decidable

module RoutingLib.Relation.Nullary where

Finite : ∀ {a} (A : Set a) → Set _
Finite A = ∃ λ n → (A ⤖ Fin n)

record Finiteₛ {a ℓ} (S : Setoid a ℓ) : Set (a ⊔ suc ℓ) where
  field
    n : ℕ
    bijection : Bijection S (setoid (Fin n))

  open Bijection bijection public
  open Setoid S renaming (Carrier to A)
  
  f⁻¹ : Fin n → A
  f⁻¹ i = proj₁ (surjective i)

  f∘f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x
  f∘f⁻¹ i = proj₂ (surjective i)

  f⁻¹∘f : ∀ x → f⁻¹ (f x) ≈ x
  f⁻¹∘f x = injective (f∘f⁻¹ (f x))

  _≟_ : B.Decidable _≈_
  x ≟ y = map′ injective cong (f x Fin.≟ f y)
  
module _ {a ℓ} {S : Setoid a ℓ} (finite : Finiteₛ S) where
  open Setoid S renaming (Carrier to A)
  open Finiteₛ finite
  
  any? : ∀ {p} {P : Pred A p} → Decidable P → P Respects _≈_ → Dec (∃ λ x → P x)
  any? P? resp with Fin.any? (λ i → P? (f⁻¹ i))
  ... | yes (i , x) = yes (f⁻¹ i , x)
  ... | no  ¬∃Pgi = no λ {(x , Px) → ¬∃Pgi (f x , resp (sym (f⁻¹∘f x)) Px)}

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
