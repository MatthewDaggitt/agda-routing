open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc; punchOut)
open import Data.Fin.Properties using (_≟_; suc-injective; punchOut-injective)
open import Data.Fin.Dec using (any?)
open import Data.Product using (_×_; ∃₂; _,_)
open import Relation.Binary.PropositionalEquality using (cong; _≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

module RoutingLib.Data.Fin.Pigeonhole where

  pigeonhole : ∀ {m n} → m < n → (f : Fin n → Fin m) →
               ∃₂ λ i j → i ≢ j × f i ≡ f j
  pigeonhole (s≤s z≤n)       f = contradiction (f zero) λ()
  pigeonhole (s≤s (s≤s m≤n)) f with any? (λ x → f zero ≟ f (suc x))
  ... | yes (j , f₀≡fⱼ₊₁) = zero , suc j , (λ()) , f₀≡fⱼ₊₁
  ... | no  ∄k[f₀≡fₖ₊₁] with pigeonhole (s≤s m≤n) ((λ j → punchOut (∄k[f₀≡fₖ₊₁] ∘ (j ,_ ))))
  ...    | (i , j , i≢j , fᵢ≡fⱼ) =
    suc i , suc j , i≢j ∘ suc-injective , punchOut-injective (∄k[f₀≡fₖ₊₁] ∘ (i ,_)) (∄k[f₀≡fₖ₊₁] ∘ (j ,_)) fᵢ≡fⱼ
