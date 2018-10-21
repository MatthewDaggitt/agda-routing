open import Data.Fin using (Fin)
open import Data.Fin.Dec using (all?)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injectiveˡ)
open import Function.Equality using (_⟨$⟩_)
open import Function.Bijection using (Bijection)
open import Level using (_⊔_)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Unary using (Pred; _∈_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Relation.Unary using (Finite)

module RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.Subset {i} {I : Set i}  where

module _ {a p ℓ} {Aᵢ : I → Set a} (_∼ᵢ_ : IRel Aᵢ ℓ) (P : Pred I p) where

------------------------------------------------------------------------
-- Types

  _∼ₛ_ : B.Rel (∀ i → Aᵢ i) (i ⊔ p ⊔ ℓ)
  x ∼ₛ y = ∀ {i} → (i∈P : i ∈ P) → x i ∼ᵢ y i

------------------------------------------------------------------------
-- Properties

  refl : Reflexive Aᵢ _∼ᵢ_ → B.Reflexive _∼ₛ_
  refl refl _ = refl

  sym : Symmetric Aᵢ _∼ᵢ_ → B.Symmetric _∼ₛ_
  sym sym x∼y i∈P = sym (x∼y i∈P)

  trans : Transitive Aᵢ _∼ᵢ_ → B.Transitive _∼ₛ_
  trans trans x∼y y∼z i∈P = trans (x∼y i∈P) (y∼z i∈P)

  module _ (finite : Finite P) where

    private
      to : ∃ P → Fin _
      to Pi = Bijection.to (proj₂ finite) ⟨$⟩ Pi

      from : Fin _ → I
      from i = proj₁ (Bijection.from (proj₂ finite) ⟨$⟩ i)

      P-from : ∀ i → from i ∈ P
      P-from i = proj₂ (Bijection.from (proj₂ finite) ⟨$⟩ i)

      from-to : ∀ {i} (i∈P : i ∈ P) → from (to (i , i∈P)) ≡ i
      from-to i∈P = ,-injectiveˡ (Bijection.left-inverse-of (proj₂ finite) (_ , i∈P))

    decidable : Decidable Aᵢ _∼ᵢ_ → B.Decidable _∼ₛ_
    decidable _∼ᵢ?_ x y with all? (λ i → x (from i) ∼ᵢ? y (from i))
    ... | yes x∼y = yes (λ i∈P → subst (λ v → x v ∼ᵢ y v) (from-to i∈P) (x∼y (to (_ , i∈P))))
    ... | no ¬x∼y = no  (λ x~ₚy → ¬x∼y (λ i → x~ₚy (P-from i)))

------------------------------------------------------------------------
-- Structures

  isEquivalence : IsIndexedEquivalence Aᵢ _∼ᵢ_ → B.IsEquivalence _∼ₛ_
  isEquivalence isEq = record
    { refl  = λ {x} → refl E.reflᵢ {x}
    ; sym   = sym   E.symᵢ
    ; trans = trans E.transᵢ
    }
    where module E = IsIndexedEquivalence isEq

  isDecEquivalence : Finite P → IsIndexedDecEquivalence Aᵢ _∼ᵢ_ → B.IsDecEquivalence _∼ₛ_
  isDecEquivalence finite isDecEq = record
    { isEquivalence = isEquivalence E.isEquivalenceᵢ
    ; _≟_           = decidable finite E._≟ᵢ_
    }
    where module E = IsIndexedDecEquivalence isDecEq

------------------------------------------------------------------------
-- Packages

module _ {c ℓ p} where

  setoid : Pred I p → IndexedSetoid I c ℓ → B.Setoid _ _
  setoid P eq = record
    { isEquivalence = isEquivalence _ P E.isEquivalenceᵢ
    }
    where module E = IndexedSetoid eq

  decSetoid : ∀ {P : Pred I p} → Finite P → IndexedDecSetoid I c ℓ → B.DecSetoid _ _
  decSetoid finite decEq = record
    { isDecEquivalence = isDecEquivalence _ _ finite E.isDecEquivalenceᵢ
    }
    where module E = IndexedDecSetoid decEq
