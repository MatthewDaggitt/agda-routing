

open import Relation.Binary

open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid

module RoutingLib.Relation.Nullary.Finite.Bijection.Setoid.Properties
  {a ℓ} {S : Setoid a ℓ} (finite : Finite S)
  where

open import Data.Fin as Fin hiding (_≟_)
import Data.Fin.Properties as Fin
open import Data.Product
open import Function
open import Relation.Unary as U using (Pred)
open import Relation.Binary.PropositionalEquality hiding (sym; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

open Setoid S renaming (Carrier to A)
open Finite finite

f⁻¹ : Fin n → A
f⁻¹ i = proj₁ (surjective i)

f∘f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x
f∘f⁻¹ i = proj₂ (surjective i)

f⁻¹∘f : ∀ x → f⁻¹ (f x) ≈ x
f⁻¹∘f x = injective (f∘f⁻¹ (f x))

_≟_ : Decidable _≈_
x ≟ y = map′ injective cong (f x Fin.≟ f y)

any? : ∀ {p} {P : Pred A p} → U.Decidable P → P Respects _≈_ → Dec (∃ λ x → P x)
any? P? resp with Fin.any? (λ i → P? (f⁻¹ i))
... | yes (i , x) = yes (f⁻¹ i , x)
... | no  ¬∃Pgi   = no λ {(x , Px) → ¬∃Pgi (f x , resp (sym (f⁻¹∘f x)) Px)}
