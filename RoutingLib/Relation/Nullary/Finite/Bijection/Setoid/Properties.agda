

open import Relation.Binary

open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid

module RoutingLib.Relation.Nullary.Finite.Bijection.Setoid.Properties
  {a ℓ} {S : Setoid a ℓ} (finite : Finite S)
  where

open import Data.Fin as Fin hiding (_≟_)
import Data.Fin.Properties as Fin
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function
open import Relation.Unary as U using (Pred)
open import Relation.Binary.PropositionalEquality hiding (sym; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

import RoutingLib.Relation.Nullary.Finite.List.Setoid as ListFinite

open Setoid S renaming (Carrier to A)
open Finite finite

_≟_ : Decidable _≈_
x ≟ y = map′ injective cong (to x Fin.≟ to y)

any? : ∀ {p} {P : Pred A p} → U.Decidable P → P Respects _≈_ → Dec (∃ λ x → P x)
any? P? resp with Fin.any? (λ i → P? (f⁻¹ i))
... | yes (i , x) = yes (f⁻¹ i , x)
... | no  ¬∃Pgi   = no λ {(x , Px) → ¬∃Pgi (to x , resp (sym (f⁻¹∘f x)) Px)}
