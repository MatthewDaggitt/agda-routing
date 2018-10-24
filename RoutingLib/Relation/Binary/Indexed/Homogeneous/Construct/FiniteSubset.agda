open import Data.Fin using (Fin)
open import Data.Fin.Dec using (all?; _∈?_)
open import Data.Fin.Subset using (Subset; _∈_; ∁)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injectiveˡ)
open import Function.Equality using (_⟨$⟩_)
open import Function.Bijection using (Bijection)
open import Level using (_⊔_)
open import Relation.Binary as B using (_⇒_)
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Relation.Nullary using (Dec; yes; no)

open import RoutingLib.Data.Fin.Subset.Properties using (x∉p⇒x∈∁p)
open import RoutingLib.Relation.Unary using (Finite)

module RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset
  {a ℓ n} (Aᵢ : Fin n → Set a) (_∼ᵢ_ : IRel Aᵢ ℓ) where

_∼[_]_ : (∀ i → Aᵢ i) → Subset n → (∀ i → Aᵢ i) → Set ℓ
x ∼[ p ] y = ∀ {i} → i ∈ p → x i ∼ᵢ y i

------------------------------------------------------------------------
-- Properties

module _ {p : Subset n} where

  refl : Reflexive Aᵢ _∼ᵢ_ → B.Reflexive _∼[ p ]_
  refl reflᵢ x = reflᵢ

  sym : Symmetric Aᵢ _∼ᵢ_ → B.Symmetric _∼[ p ]_
  sym symᵢ x∼y i∈P = symᵢ (x∼y i∈P)

  trans : Transitive Aᵢ _∼ᵢ_ → B.Transitive _∼[ p ]_
  trans transᵢ x∼y y∼z i∈P = transᵢ (x∼y i∈P) (y∼z i∈P)

  postulate decidable : Decidable Aᵢ _∼ᵢ_ → ∀ x y → Dec (x ∼[ p ] y)

module _ (p : Subset n) where

  isEquivalence : IsIndexedEquivalence Aᵢ _∼ᵢ_ → B.IsEquivalence _∼[ p ]_
  isEquivalence isEq = record
    { refl  = λ {x} → refl  Eq.reflᵢ {x}
    ; sym   = sym   Eq.symᵢ
    ; trans = trans Eq.transᵢ
    } where module Eq = IsIndexedEquivalence isEq
  
  isDecEquivalence : IsIndexedDecEquivalence Aᵢ _∼ᵢ_ → B.IsDecEquivalence _∼[ p ]_
  isDecEquivalence isEq = record
    { isEquivalence = isEquivalence Eq.isEquivalenceᵢ
    ; _≟_           = decidable Eq._≟ᵢ_
    } where module Eq = IsIndexedDecEquivalence isEq