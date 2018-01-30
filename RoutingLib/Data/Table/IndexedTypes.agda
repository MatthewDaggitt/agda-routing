open import Data.Fin using (Fin)
open import Data.Product using (∃; _×_)
open import Data.List using (List)
import Data.List.Any.Membership as Memb
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using () renaming (Pred to Predᵤ; _∈_ to _∈ᵤ_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Table using (Table)

module RoutingLib.Data.Table.IndexedTypes {a ℓ n} (S : Table (Setoid a ℓ) n) where

  -- Types
  
  Mᵢ : Fin n → Set a
  Mᵢ i = Setoid.Carrier (S i)
  
  M : Set a
  M = ∀ i → Mᵢ i
  -- Equality

  module _ {i : Fin n} where
    open Setoid (S i)
      renaming 
      ( _≈_       to _≈ᵢ_
      ; reflexive to ≈ᵢ-reflexive
      ; refl      to ≈ᵢ-refl
      ; sym       to ≈ᵢ-sym
      ; trans     to ≈ᵢ-trans
      ) public

  _≈_ : Rel M ℓ
  s ≈ t = ∀ i → s i ≈ᵢ t i

  _≉_ : Rel M ℓ
  s ≉ t = ¬ s ≈ t
  
  ≈-refl : Reflexive _≈_
  ≈-refl i = ≈ᵢ-refl

  ≈-sym : Symmetric _≈_
  ≈-sym s≈t i = ≈ᵢ-sym (s≈t i)

  ≈-trans : Transitive _≈_
  ≈-trans r≈s s≈t i = ≈ᵢ-trans (r≈s i) (s≈t i)

  ≈-cong : ∀ {b} {A : Set b} (f : A → M) {x y} → x ≡ y → f x ≈ f y
  ≈-cong f refl i = ≈ᵢ-refl
  
  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }

  M-setoid : Setoid a ℓ
  M-setoid = record
    { Carrier       = M
    ; _≈_           = _≈_
    ; isEquivalence = ≈-isEquivalence
    }

  -- Ordering Relation
  record M-poset p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      _≼ᵢ_ : ∀ {i} → Rel (Mᵢ i) p
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

    _≼_ : Rel M p
    _≼_ x y = ∀ i → x i ≼ᵢ y i

    ≼-refl : Reflexive _≼_
    ≼-refl i = ≼ᵢ-refl

    ≼-reflexive : _≈_ ⇒ _≼_
    ≼-reflexive x≈y i = ≼ᵢ-reflexive (x≈y i)

    ≼-trans : Transitive _≼_
    ≼-trans x≼y y≼z i = ≼ᵢ-trans (x≼y i) (y≼z i)

    ≼-antisym : Antisymmetric _≈_ _≼_
    ≼-antisym x≼y y≼x i = ≼ᵢ-antisym (x≼y i) (y≼x i)
  

  open Memb M-setoid using () renaming (_∈_ to _∈L_)
  
  -- Predicates and relations over predicates

  Pred : ∀ p → Set (a ⊔ lsuc p)
  Pred p = ∀ i → Predᵤ (Mᵢ i) p

  _∈_ : ∀ {p} → M → Pred p → Set p
  t ∈ P = ∀ i → t i ∈ᵤ P i

  _∉_ : ∀ {p} → M → Pred p → Set p
  t ∉ P = ¬ (t ∈ P)

  _⊆_ : ∀ {p} → Rel (Pred p) (a ⊔ p)
  P ⊆ Q = ∀ {t} → t ∈ P → t ∈ Q

  _⊂_ : ∀ {p} → Rel (Pred p) (a ⊔ p)
  P ⊂ Q = P ⊆ Q × ∃ λ t → t ∈ Q × ¬ (t ∈ P)

  ｛_｝ : M → Predᵤ M ℓ
  ｛ t ｝ = t ≈_

  isSingleton : ∀ {p} → M → Predᵤ (Pred p) (a ⊔ p ⊔ ℓ)
  isSingleton t P = t ∈ P × ∀ s → s ∈ P → t ≈ s
  
  Finite-Pred : ∀ {p} (P : Pred p) → Set (a ⊔ p ⊔ ℓ)
  Finite-Pred P = ∃ λ (xs : List M) → ∀ {x} → x ∈ P → x ∈L xs
