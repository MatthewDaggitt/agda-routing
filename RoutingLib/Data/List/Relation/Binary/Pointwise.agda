open import Algebra.Core using (Op₂)
open import Data.List
import Data.List.Properties as ListProperties
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; []; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Fin using (Fin; zero; suc; cast; toℕ)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary using (REL; Rel; Reflexive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

module RoutingLib.Data.List.Relation.Binary.Pointwise where

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b
    
-------------------------------------------------------------------
-- Reflexive properties

reflexive-≡ : (_~_ : Rel A ℓ) → Reflexive _~_ → _≡_ ⇒ Pointwise _~_
reflexive-≡ _ ref refl = PW.refl ref

foldr⁺ : ∀ (_~_ : REL A B ℓ) {_⊕ᵃ_ : Op₂ A} {_⊕ᵇ_ : Op₂ B} →
         (∀ {w x y z} → w ~ x → y ~ z → (w ⊕ᵃ y) ~ (x ⊕ᵇ z)) →
         ∀ {xs ys e f} → e ~ f → Pointwise _~_ xs ys →
         foldr _⊕ᵃ_ e xs ~ foldr _⊕ᵇ_ f ys
foldr⁺ _ _    e~f []            = e~f
foldr⁺ _ pres e~f (x~y ∷ xs~ys) = pres x~y (foldr⁺ _ pres e~f xs~ys)

map-tabulate : ∀ {_~_ : Rel B ℓ} → Reflexive _~_ → ∀ {n} (f : A → B) (g : Fin n → A) →
               Pointwise _~_ (map f (tabulate g)) (tabulate (f ∘ g))
map-tabulate ref f g = reflexive-≡ _ ref (ListProperties.map-tabulate g f)

module _ {_∼_ : REL A B ℓ} where

  lookup⁻ : ∀ {xs ys} (|xs|≡|ys| : length xs ≡ length ys) →
            (∀ {i j} → toℕ i ≡ toℕ j → lookup xs i ∼ lookup ys j) →
            Pointwise _∼_ xs ys
  lookup⁻ {[]}     {[]}     _             _  = []
  lookup⁻ {x ∷ xs} {y ∷ ys} |x∷xs|≡|y∷ys| eq = eq {zero} refl ∷ lookup⁻ (suc-injective |x∷xs|≡|y∷ys|) (eq ∘ cong suc)

  lookup⁺ : ∀ {xs ys} (xs∼ys : Pointwise _∼_ xs ys) → ∀ i → lookup xs i ∼ lookup ys (cast (PW.Pointwise-length xs∼ys) i)
  lookup⁺ (x∼y ∷ xs∼ys) zero    = x∼y
  lookup⁺ (x∼y ∷ xs∼ys) (suc i) = lookup⁺ xs∼ys i
