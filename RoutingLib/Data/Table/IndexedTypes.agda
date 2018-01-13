open import Data.Fin using (Fin)
open import Data.Product using (∃; _×_)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary
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

  ≈-refl : Reflexive _≈_
  ≈-refl i = ≈ᵢ-refl

  ≈-sym : Symmetric _≈_
  ≈-sym s≈t i = ≈ᵢ-sym (s≈t i)

  ≈-trans : Transitive _≈_
  ≈-trans r≈s s≈t i = ≈ᵢ-trans (r≈s i) (s≈t i)
  
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

  
  -- Predicates and relations over predicates

  Pred : ∀ p → Set (a ⊔ lsuc p)
  Pred p = ∀ i → Predᵤ (Mᵢ i) p

  _∈_ : ∀ {p} → M → Pred p → Set p
  t ∈ P = ∀ i → t i ∈ᵤ P i

  _⊆_ : ∀ {p} → Rel (Pred p) (a ⊔ p)
  P ⊆ Q = ∀ t → t ∈ P → t ∈ Q

  _⊂_ : ∀ {p} → Rel (Pred p) (a ⊔ p)
  P ⊂ Q = P ⊆ Q × ∃ λ t → t ∈ Q × ¬ (t ∈ P)

  ｛_｝ : M → Predᵤ M ℓ
  ｛ t ｝ = t ≈_

  Singleton-t : ∀ {p} → M → Predᵤ (Pred p) (a ⊔ p ⊔ ℓ)
  Singleton-t t P = t ∈ P × ∀ s → s ∈ P → t ≈ s
  
