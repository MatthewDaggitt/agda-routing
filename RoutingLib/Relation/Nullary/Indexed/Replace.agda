open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module RoutingLib.Relation.Nullary.Indexed.Replace
  {i a} {I : Set i} (Aᵢ : I → Set a) (_≟I_ : Decidable {A = I} _≡_) where

open import Relation.Unary using (_∈_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Unary.Indexed using (IPred; _∈ᵢ_)

private
  A : Set _
  A = ∀ i → Aᵢ i

replace : A → ∀ {i} (xᵢ : Aᵢ i) → A
replace x {i} xᵢ j with i ≟I j
... | yes refl = xᵢ
... | no  _    = x j

∈-replace : ∀ {p} (P : IPred Aᵢ p) {x i} {xᵢ : Aᵢ i} → x ∈ᵢ P → xᵢ ∈ P i → replace x xᵢ ∈ᵢ P
∈-replace P {i = i} x∈P xᵢ∈P j with i ≟I j
... | yes refl = xᵢ∈P
... | no  _    = x∈P j

≡-replace : ∀ x {i} (xᵢ : Aᵢ i) → replace x xᵢ i ≡ xᵢ
≡-replace x {i} xᵢ with i ≟I i
... | yes refl = refl
... | no  i≢i  = contradiction refl i≢i
