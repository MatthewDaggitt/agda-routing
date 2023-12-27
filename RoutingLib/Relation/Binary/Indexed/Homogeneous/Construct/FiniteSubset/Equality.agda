open import Data.Fin using (Fin)
open import Data.Fin.Properties using (all?)
open import Data.Fin.Subset using (Subset; _∈_; ∁)
open import Data.Fin.Subset.Properties using (x∉p⇒x∈∁p; _∈?_)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injectiveˡ)
open import Level using (_⊔_)
import Relation.Binary as B
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import RoutingLib.Relation.Unary using (Finite)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset as FiniteSubset

module RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality
  {n a ℓ} (S : IndexedSetoid (Fin n) a ℓ) where

open IndexedSetoid S using (_≈ᵢ_; _≈_) renaming ( Carrierᵢ to Aᵢ; Carrier to A)

open FiniteSubset Aᵢ _≈ᵢ_ public
  using () renaming (_∼[_]_ to _≈[_]_)

_≉[_]_ : A → Subset n → A → Set ℓ
x ≉[ p ] y = ¬ (x ≈[ p ] y)

≈ₛ-isEquivalence : ∀ p → B.IsEquivalence _≈[ p ]_
≈ₛ-isEquivalence p = FiniteSubset.isEquivalence Aᵢ _≈ᵢ_ p (IndexedSetoid.isEquivalenceᵢ S)

≈ₛ-setoid : ∀ p → B.Setoid _ _
≈ₛ-setoid p = record
  { isEquivalence = ≈ₛ-isEquivalence p
  }

module _ {p : Subset n} where

  open B.IsEquivalence (≈ₛ-isEquivalence p) public
    using ()
    renaming
    ( refl  to ≈ₛ-refl
    ; sym   to ≈ₛ-sym
    ; trans to ≈ₛ-trans
    )


  ≈⇒≈ₛ : _≈_ B.⇒ (_≈[ p ]_)
  ≈⇒≈ₛ x≈y {i} i∈p = x≈y i

  ≈ₛ+≈₋ₛ⇒≈ : ∀ {x y} → x ≈[ p ] y → x ≈[ ∁ p ] y → x ≈ y
  ≈ₛ+≈₋ₛ⇒≈ ≈ₛ ≈₋ₛ i with i ∈? p
  ... | yes i∈p = ≈ₛ i∈p
  ... | no  i∉p = ≈₋ₛ (x∉p⇒x∈∁p i∉p)
