open import Level using (_⊔_)
open import Relation.Binary using (DecSetoid; Rel; Decidable)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using () renaming (Decidable to Decidableᵤ)
open import Data.Product using (Σ; ∃; _,_; _×_; proj₁)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ)
open import Algebra.FunctionProperties using (Op₂)
open import Data.List.All using ([]; _∷_)
open import Data.List.All.Properties using (¬Any⇒All¬)
open import Function using (_∘_)

open import RoutingLib.Data.List using (dfilter)
open import RoutingLib.Data.List.All using ([]; _∷_)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)

module RoutingLib.Data.List.Uniset {c ℓ} (DS : DecSetoid c ℓ) where
  
  open DecSetoid DS renaming (Carrier to A; setoid to S)
  open import Data.List.Any.Membership S using () renaming (_∈_ to _∈ₗ_)
  open import RoutingLib.Data.List.Membership.Setoid.Properties using (∈-dec)
  open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (dfilter!⁺)

  private

    _≉_ : Rel A ℓ
    x ≉ y = ¬ (x ≈ y)

    _≉?_ : Decidable _≉_
    x ≉? y with x ≟ y
    ... | yes x≈y = no (λ x≉y → x≉y x≈y)
    ... | no  x≉y = yes x≉y

    _∈ₗ?_ : Decidable _∈ₗ_
    _∈ₗ?_ = ∈-dec S _≟_


  -- Main type

  Uniset : Set _
  Uniset = Σ (List A) (Unique S)

  ∅ : Uniset
  ∅ = [] , []


  -- Membership

  infix 4 _∈_ _∉_

  _∈_ : A → Uniset → Set _
  x ∈ X = x ∈ₗ proj₁ X

  _∉_ : A → Uniset → Set _
  x ∉ X = ¬ (x ∈ X)


  -- Relations

  infix 4 _⊆_ _⊈_ _⊂_ _⊄_

  _⊆_ : Rel Uniset _
  X ⊆ Y = ∀ {x} → x ∈ X → x ∈ Y

  _⊈_ : Rel Uniset _
  X ⊈ Y = ¬ (X ⊆ Y)
  
  _⊂_ : Rel Uniset _
  X ⊂ Y = X ⊆ Y × ∃ λ y → y ∈ Y × y ∉ X

  _⊄_ : Rel Uniset _
  X ⊄ Y = ¬ (X ⊂ Y)


  -- Mutable operations

  filter : ∀ {p} {P : A → Set p} → Decidableᵤ P → Uniset → Uniset
  filter P? (xs , xs!) = dfilter P? xs , dfilter!⁺ S P? xs! 
  
  add : A → Uniset → Uniset
  add x (xs , xs!) with x ∈ₗ? xs
  ... | yes _    = xs , xs!
  ... | no  x∉xs = x ∷ xs , ¬Any⇒All¬ _ x∉xs ∷ xs!

  remove : A → Uniset → Uniset
  remove x X = filter (x ≉?_) X

  _∪_ : Op₂ Uniset
  ([]     , _)          ∪ Y = Y
  (x ∷ xs , x∉xs ∷ xs!) ∪ Y = add x ((xs , xs!) ∪ Y)

  _∩_ : Op₂ Uniset
  X ∩ (ys , ys!) = filter (_∈ₗ? ys) X 


  -- Properties

  size : Uniset → ℕ
  size X = length (proj₁ X)


  -- Enumeration

  IsEnumeration : Uniset → Set _
  IsEnumeration X = ∀ x → x ∈ X

  record Enumeration : Set (c ⊔ ℓ) where

    field
      X : Uniset
      isEnumeration : IsEnumeration X
