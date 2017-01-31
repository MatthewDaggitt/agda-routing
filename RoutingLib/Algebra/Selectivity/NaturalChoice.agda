

open import Relation.Binary using (Rel; Setoid; Total; Reflexive; Antisymmetric; Symmetric; Transitive)
open import Algebra.FunctionProperties.Core using (Op₂)
open import Algebra.FunctionProperties hiding (Op₂)
open import Data.Sum using (inj₁; inj₂)

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Relation.Binary.RespectedBy
open import RoutingLib.Relation.Binary.Orders

module RoutingLib.Algebra.Selectivity.NaturalChoice {a ℓ} {A : Set a} {_≤_ : Rel A ℓ} (total : Total _≤_) where

  _•_ : Op₂ A
  x • y with total x y
  ... | inj₁ x≤y = x
  ... | inj₂ y≤x = y

  ----------------
  -- Properties --
  ----------------

  module Properties {ℓ₂} (_≈_ : Rel A ℓ₂) (refl : Reflexive _≈_) where

    sel : Selective _≈_ _•_
    sel x y with total x y
    ... | inj₁ x≤y = inj₁ refl
    ... | inj₂ y≤x = inj₂ refl

    comm : Antisymmetric _≈_ _≤_ → Commutative _≈_ _•_
    comm antisym x y with total x y | total y x
    ... | inj₁ x≤y | inj₁ y≤x = antisym x≤y y≤x
    ... | inj₁ _   | inj₂ _   = refl
    ... | inj₂ _   | inj₁ _   = refl
    ... | inj₂ y≤x | inj₂ x≤y = antisym y≤x x≤y

    -- If Agda's rememberence of pattern matching was clever this could be a lot shorter (cut down to 10 lines)
    assoc : Antisymmetric _≈_ _≤_ → Transitive _≤_ → Associative _≈_ _•_
    assoc antisym trans x y z with total x y | total x z | total y z
    assoc antisym trans x y z | inj₁ x≤y | inj₁ x≤z | inj₁ y≤z with total x z | total x y
    ... | inj₁ x≤z₂ | inj₁ x≤y₂ = refl
    ... | inj₁ x≤z₂ | inj₂ y≤x  = antisym x≤y y≤x
    ... | inj₂ z≤x  | inj₁ x≤y₂ = antisym z≤x (trans x≤y y≤z)
    ... | inj₂ z≤x  | inj₂ y≤x  = antisym (trans z≤x x≤y) (trans y≤x x≤z)
    assoc antisym trans x y z | inj₁ x≤y | inj₁ x≤z | inj₂ z≤y with total x z
    ... | inj₁ _                = refl
    ... | inj₂ _                = refl
    assoc antisym trans x y z | inj₁ x≤y | inj₂ z≤x | inj₁ y≤z with total x z | total x y
    ... | inj₁ x≤z  | inj₁ x≤y₂ = refl
    ... | inj₁ x≤z  | inj₂ y≤x  = antisym x≤y (trans y≤z z≤x)
    ... | inj₂ z≤x₂ | inj₁ x≤y₂ = antisym z≤x (trans x≤y y≤z)
    ... | inj₂ z≤x₂ | inj₂ y≤x  = antisym (trans z≤x x≤y) y≤z
    assoc antisym trans x y z | inj₁ x≤y | inj₂ z≤x | inj₂ z≤y with total x z
    ... | inj₁ _                = refl
    ... | inj₂ _                = refl
    assoc antisym trans x y z | inj₂ y≤x | inj₁ x≤z | inj₁ y≤z with total y z | total x y
    ... | inj₁ y≤z₂ | inj₁ x≤y  = antisym y≤x x≤y
    ... | inj₁ y≤z₂ | inj₂ y≤x₂ = refl
    ... | inj₂ z≤y  | inj₁ x≤y  = antisym (trans z≤y y≤x) (trans x≤y y≤z)
    ... | inj₂ z≤y  | inj₂ y≤x₂ = antisym z≤y (trans y≤x x≤z)
    assoc antisym trans x y z | inj₂ y≤x | inj₁ x≤z | inj₂ z≤y with total y z | total x z
    ... | inj₁ y≤z  | inj₁ x≤z₂ = antisym y≤x (trans x≤z z≤y)
    ... | inj₁ y≤z  | inj₂ z≤x  = antisym (trans y≤x x≤z) z≤y
    ... | inj₂ z≤y₂ | inj₁ x≤z₂ = antisym (trans z≤y y≤x) x≤z
    ... | inj₂ z≤y₂ | inj₂ z≤x  = refl
    assoc antisym trans x y z | inj₂ y≤x | inj₂ z≤x | inj₁ y≤z with total y z | total x y
    ... | inj₁ y≤z₂ | inj₁ x≤y  = antisym (trans y≤z z≤x) x≤y
    ... | inj₁ y≤z₂ | inj₂ y≤x₂ = refl
    ... | inj₂ z≤y  | inj₁ x≤y  = antisym (trans z≤y y≤x) (trans x≤y y≤z)
    ... | inj₂ z≤y  | inj₂ y≤x₂ = antisym z≤y y≤z
    assoc antisym trans x y z | inj₂ y≤x | inj₂ z≤x | inj₂ z≤y  with total y z | total x z
    ... | inj₁ y≤z  | inj₁ x≤z  = antisym (trans y≤z z≤x) (trans x≤z z≤y)
    ... | inj₁ y≤z  | inj₂ z≤x₂ = antisym y≤z z≤y
    ... | inj₂ z≤y₂ | inj₁ x≤z  = antisym (trans z≤y y≤x) x≤z
    ... | inj₂ z≤y₂ | inj₂ z≤x₂ = refl

    absorbs : Antisymmetric _≈_ _≤_ → ∀ {_◦_} → _IncreasingOver_ _≈_ _◦_ _≤_ → _Absorbs_ _≈_ _•_ _◦_
    absorbs antisym {_◦_} ◦-inc-≤ x y with total x (x ◦ y)
    ... | inj₁ x≤x◦y = refl
    ... | inj₂ x◦y≤x = antisym x◦y≤x ◦-inc-≤

    -- Identities and annihilators

    idₗ : Antisymmetric _≈_ _≤_ → ∀ {⊥} → Top _≤_ ⊥ → LeftIdentity _≈_ ⊥ _•_
    idₗ antisym {⊥} ⊥-top x with total ⊥ x
    ... | inj₁ ⊥≤x = antisym ⊥≤x ⊥-top
    ... | inj₂ x≤⊥ = refl

    idᵣ : Antisymmetric _≈_ _≤_ → ∀ {⊥} → Top _≤_ ⊥ → RightIdentity _≈_ ⊥ _•_
    idᵣ antisym {⊥} ⊥-top x with total x ⊥
    ... | inj₁ x≤⊥ = refl
    ... | inj₂ ⊥≤x = antisym ⊥≤x ⊥-top

    anₗ : Antisymmetric _≈_ _≤_ → ∀ {⊥} → Bottom _≤_ ⊥ → LeftZero _≈_ ⊥ _•_
    anₗ antisym {⊥} ⊥-bottom x with total ⊥ x
    ... | inj₁ ⊥≤x = refl
    ... | inj₂ x≤⊥ = antisym x≤⊥ ⊥-bottom

    anᵣ : Antisymmetric _≈_ _≤_ → ∀ {⊥} → Bottom _≤_ ⊥ → RightZero _≈_ ⊥ _•_
    anᵣ antisym {⊥} ⊥-bottom x with total x ⊥
    ... | inj₁ x≤⊥ = antisym x≤⊥ ⊥-bottom
    ... | inj₂ ⊥≤x = refl

    -- Other

    preserves : Symmetric _≈_ → Antisymmetric _≈_ _≤_ → _≤_ RespectedBy _≈_ → _•_ Preserves _≈_
    preserves sym antisym resp {w} {x} {y} {z} w≈x y≈z with total w y | total x z
    ... | inj₁ w≤y | inj₁ x≤z = w≈x
    ... | inj₁ w≤y | inj₂ z≤x = antisym (resp refl y≈z w≤y) (resp refl (sym w≈x) z≤x)
    ... | inj₂ y≤w | inj₁ x≤z = antisym (resp refl w≈x y≤w) (resp refl (sym y≈z) x≤z)
    ... | inj₂ y≤w | inj₂ z≤x = y≈z

  open Properties public
