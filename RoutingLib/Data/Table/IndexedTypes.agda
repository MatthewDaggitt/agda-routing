open import Data.Fin using (Fin)
open import Data.Product using (∃; _×_)
open import Data.List using (List)
import Data.List.Membership.Setoid as Membership
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using () renaming (Pred to Predᵤ; _∈_ to _∈ᵤ_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Table using (Table)

module RoutingLib.Data.Table.IndexedTypes {a ℓ n} (𝕊ᵢ : Table (Setoid a ℓ) n) where

  -- Types
  
  Sᵢ : Fin n → Set a
  Sᵢ i = Setoid.Carrier (𝕊ᵢ i)
  
  S : Set a
  S = ∀ i → Sᵢ i
  
  -- Equality

  module _ {i : Fin n} where
    open Setoid (𝕊ᵢ i)
      renaming 
      ( _≈_       to _≈ᵢ_
      ; reflexive to ≈ᵢ-reflexive
      ; refl      to ≈ᵢ-refl
      ; sym       to ≈ᵢ-sym
      ; trans     to ≈ᵢ-trans
      ) public

  _≈_ : Rel S ℓ
  s ≈ t = ∀ i → s i ≈ᵢ t i

  _≉_ : Rel S ℓ
  s ≉ t = ¬ s ≈ t
  
  ≈-refl : Reflexive _≈_
  ≈-refl i = ≈ᵢ-refl

  ≈-sym : Symmetric _≈_
  ≈-sym s≈t i = ≈ᵢ-sym (s≈t i)

  ≈-trans : Transitive _≈_
  ≈-trans r≈s s≈t i = ≈ᵢ-trans (r≈s i) (s≈t i)

  ≈-cong : ∀ {b} {A : Set b} (f : A → S) {x y} → x ≡ y → f x ≈ f y
  ≈-cong f refl i = ≈ᵢ-refl
  
  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }

  𝕊 : Setoid a ℓ
  𝕊 = record
    { Carrier       = S
    ; _≈_           = _≈_
    ; isEquivalence = ≈-isEquivalence
    }

  -- Ordering Relation
  record M-poset p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      _≼ᵢ_ : ∀ {i} → Rel (Sᵢ i) p
      isPartialOrderᵢ : ∀ i → IsPartialOrder (_≈ᵢ_ {i}) _≼ᵢ_

    module _ {i : Fin n} where
      open IsPartialOrder (isPartialOrderᵢ i)
        renaming
        ( isPreorder to ≼ᵢ-isPreorder
        ; antisym    to ≼ᵢ-antisym
        ) public
      open IsPreorder ≼ᵢ-isPreorder
        using ()
        renaming
        ( reflexive to ≼ᵢ-reflexive
        ; trans     to ≼ᵢ-trans
        ) public

    ≼ᵢ-refl : ∀ {i} → Reflexive (_≼ᵢ_ {i})
    ≼ᵢ-refl {i} = ≼ᵢ-reflexive ≈ᵢ-refl

    _≼_ : Rel S p
    _≼_ x y = ∀ i → x i ≼ᵢ y i

    ≼-refl : Reflexive _≼_
    ≼-refl i = ≼ᵢ-refl

    ≼-reflexive : _≈_ ⇒ _≼_
    ≼-reflexive x≈y i = ≼ᵢ-reflexive (x≈y i)

    ≼-trans : Transitive _≼_
    ≼-trans x≼y y≼z i = ≼ᵢ-trans (x≼y i) (y≼z i)

    ≼-antisym : Antisymmetric _≈_ _≼_
    ≼-antisym x≼y y≼x i = ≼ᵢ-antisym (x≼y i) (y≼x i)

    ≼-isPreorder : IsPreorder _≈_ _≼_
    ≼-isPreorder = record
      { isEquivalence = ≈-isEquivalence
      ; reflexive     = ≼-reflexive
      ; trans         = ≼-trans
      }
    
    ≼-isPartialOrder : IsPartialOrder _≈_ _≼_
    ≼-isPartialOrder = record
      { isPreorder = ≼-isPreorder
      ; antisym    = ≼-antisym
      }

    ≼-poset : Poset _ _ _
    ≼-poset = record { isPartialOrder = ≼-isPartialOrder }
    
  open Membership 𝕊 using () renaming (_∈_ to _∈L_)
  
  -- Predicates and relations over predicates

  Pred : ∀ p → Set (a ⊔ lsuc p)
  Pred p = ∀ i → Predᵤ (Sᵢ i) p

  _∈_ : ∀ {p} → S → Pred p → Set p
  t ∈ P = ∀ i → t i ∈ᵤ P i

  _∉_ : ∀ {p} → S → Pred p → Set p
  t ∉ P = ¬ (t ∈ P)

  _⊆_ : ∀ {p} → Rel (Pred p) (a ⊔ p)
  P ⊆ Q = ∀ {t} → t ∈ P → t ∈ Q

  _⊂_ : ∀ {p} → Rel (Pred p) (a ⊔ p)
  P ⊂ Q = P ⊆ Q × ∃ λ t → t ∈ Q × ¬ (t ∈ P)

  ｛_｝ : S → Predᵤ S ℓ
  ｛ t ｝ = t ≈_

  IsSingleton : ∀ {p} → S → Predᵤ (Pred p) (a ⊔ p ⊔ ℓ)
  IsSingleton t P = t ∈ P × ∀ s → s ∈ P → t ≈ s
  
  Finite-Pred : ∀ {p} (P : Pred p) → Set (a ⊔ p ⊔ ℓ)
  Finite-Pred P = ∃ λ (xs : List S) → ∀ {x} → x ∈ P → x ∈L xs
