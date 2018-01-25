open import Data.List using ([]; _∷_; tabulate)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc)
open import Function using (_∘_)
open import Relation.Binary using (REL; Rel; Reflexive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to PW)

module RoutingLib.Data.List.Relation.Pointwise where

  ≡⇒Rel≈ : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} → Reflexive _≈_ → _≡_ ⇒ PW _≈_
  ≡⇒Rel≈ ref {[]}     refl = []
  ≡⇒Rel≈ ref {x ∷ xs} refl = ref ∷ ≡⇒Rel≈ ref refl

  tabulate⁺ : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} →
              ∀ {n} {f : Fin n → A} {g : Fin n → B} → (∀ i → f i ~ g i) →
              PW _~_ (tabulate f) (tabulate g)
  tabulate⁺ {n = zero}  f~g = []
  tabulate⁺ {n = suc n} f~g = (f~g zero) ∷ tabulate⁺ (f~g ∘ suc)
