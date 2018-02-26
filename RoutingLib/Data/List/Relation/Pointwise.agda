open import Algebra.FunctionProperties using (Op₂)
open import Data.List using ([]; _∷_; foldr)
open import Function using (_∘_)
open import Relation.Binary using (REL; Rel; Reflexive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.List.Pointwise using (Pointwise; []; _∷_)

module RoutingLib.Data.List.Relation.Pointwise where

  ≡⇒Rel≈ : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} → Reflexive _≈_ → _≡_ ⇒ Pointwise _≈_
  ≡⇒Rel≈ ref {[]}     refl = []
  ≡⇒Rel≈ ref {x ∷ xs} refl = ref ∷ ≡⇒Rel≈ ref refl

  foldr-All₂ : ∀ {a b ℓ} {A : Set a} {B : Set b} (_~_ : REL A B ℓ)
             {_⊕ᵃ_ : Op₂ A} {_⊕ᵇ_ : Op₂ B} → 
             (∀ {w x y z} → w ~ x → y ~ z → (w ⊕ᵃ y) ~ (x ⊕ᵇ z)) →
             ∀ {xs ys e f} → e ~ f → Pointwise _~_ xs ys →
             foldr _⊕ᵃ_ e xs ~ foldr _⊕ᵇ_ f ys
  foldr-All₂ _ _    e~f []            = e~f
  foldr-All₂ _ pres e~f (x~y ∷ xs~ys) = pres x~y (foldr-All₂ _ pres e~f xs~ys)
