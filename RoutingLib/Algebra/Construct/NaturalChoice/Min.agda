open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.Lattice using (Minimum; Maximum)

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Relation.Binary

module RoutingLib.Algebra.Construct.NaturalChoice.Min
  {a ℓ} {A : Set a} {_≤_ : Rel A ℓ} (total : Total _≤_) where

min : Op₂ A
min x y with total x y
... | inj₁ x≤y = x
... | inj₂ y≤x = y

----------------------------------------------------------------------------
-- Algebraic properties

module _ {ℓ₂} (_≈_ : Rel A ℓ₂) where

  sel : Reflexive _≈_ → Selective _≈_ min
  sel refl x y with total x y
  ... | inj₁ x≤y = inj₁ refl
  ... | inj₂ y≤x = inj₂ refl

module _ {ℓ₂} {_≈_ : Rel A ℓ₂} where

  cong : Symmetric _≈_ → Antisymmetric _≈_ _≤_ →
         _≤_ Respects₂ _≈_ → Congruent₂ _≈_ min
  cong sym antisym (respˡ , respʳ) {w} {x} {y} {z} w≈x y≈z with total w y | total x z
  ... | inj₁ w≤y | inj₁ x≤z = w≈x
  ... | inj₁ w≤y | inj₂ z≤x = antisym (respˡ y≈z w≤y) (respˡ (sym w≈x) z≤x)
  ... | inj₂ y≤w | inj₁ x≤z = antisym (respˡ w≈x y≤w) (respˡ (sym y≈z) x≤z)
  ... | inj₂ y≤w | inj₂ z≤x = y≈z

  comm : Reflexive _≈_ → Antisymmetric _≈_ _≤_ → Commutative _≈_ min
  comm refl antisym x y with total x y | total y x
  ... | inj₁ x≤y | inj₁ y≤x = antisym x≤y y≤x
  ... | inj₁ _   | inj₂ _   = refl
  ... | inj₂ _   | inj₁ _   = refl
  ... | inj₂ y≤x | inj₂ x≤y = antisym y≤x x≤y

  assoc : Reflexive _≈_ → Transitive _≤_ →
          Antisymmetric _≈_ _≤_ → Associative _≈_ min
  assoc refl trans antisym x y z with total x y | total x z | total y z
  assoc refl trans antisym x y z | inj₁ x≤y | inj₁ x≤z | inj₁ y≤z with total x z | total x y
  ... | inj₁ x≤z₂ | inj₁ x≤y₂ = refl
  ... | inj₁ x≤z₂ | inj₂ y≤x  = antisym x≤y y≤x
  ... | inj₂ z≤x  | inj₁ x≤y₂ = antisym z≤x (trans x≤y y≤z)
  ... | inj₂ z≤x  | inj₂ y≤x  = antisym (trans z≤x x≤y) (trans y≤x x≤z)
  assoc refl trans antisym x y z | inj₁ x≤y | inj₁ x≤z | inj₂ z≤y with total x z
  ... | inj₁ _                = refl
  ... | inj₂ _                = refl
  assoc refl trans antisym x y z | inj₁ x≤y | inj₂ z≤x | inj₁ y≤z with total x z | total x y
  ... | inj₁ x≤z  | inj₁ x≤y₂ = refl
  ... | inj₁ x≤z  | inj₂ y≤x  = antisym x≤y (trans y≤z z≤x)
  ... | inj₂ z≤x₂ | inj₁ x≤y₂ = antisym z≤x (trans x≤y y≤z)
  ... | inj₂ z≤x₂ | inj₂ y≤x  = antisym (trans z≤x x≤y) y≤z
  assoc refl trans antisym x y z | inj₁ x≤y | inj₂ z≤x | inj₂ z≤y with total x z
  ... | inj₁ _                = refl
  ... | inj₂ _                = refl
  assoc refl trans antisym x y z | inj₂ y≤x | inj₁ x≤z | inj₁ y≤z with total y z | total x y
  ... | inj₁ y≤z₂ | inj₁ x≤y  = antisym y≤x x≤y
  ... | inj₁ y≤z₂ | inj₂ y≤x₂ = refl
  ... | inj₂ z≤y  | inj₁ x≤y  = antisym (trans z≤y y≤x) (trans x≤y y≤z)
  ... | inj₂ z≤y  | inj₂ y≤x₂ = antisym z≤y (trans y≤x x≤z)
  assoc refl trans antisym x y z | inj₂ y≤x | inj₁ x≤z | inj₂ z≤y with total y z | total x z
  ... | inj₁ y≤z  | inj₁ x≤z₂ = antisym y≤x (trans x≤z z≤y)
  ... | inj₁ y≤z  | inj₂ z≤x  = antisym (trans y≤x x≤z) z≤y
  ... | inj₂ z≤y₂ | inj₁ x≤z₂ = antisym (trans z≤y y≤x) x≤z
  ... | inj₂ z≤y₂ | inj₂ z≤x  = refl
  assoc refl trans antisym x y z | inj₂ y≤x | inj₂ z≤x | inj₁ y≤z with total y z | total x y
  ... | inj₁ y≤z₂ | inj₁ x≤y  = antisym (trans y≤z z≤x) x≤y
  ... | inj₁ y≤z₂ | inj₂ y≤x₂ = refl
  ... | inj₂ z≤y  | inj₁ x≤y  = antisym (trans z≤y y≤x) (trans x≤y y≤z)
  ... | inj₂ z≤y  | inj₂ y≤x₂ = antisym z≤y y≤z
  assoc refl trans antisym x y z | inj₂ y≤x | inj₂ z≤x | inj₂ z≤y  with total y z | total x z
  ... | inj₁ y≤z  | inj₁ x≤z  = antisym (trans y≤z z≤x) (trans x≤z z≤y)
  ... | inj₁ y≤z  | inj₂ z≤x₂ = antisym y≤z z≤y
  ... | inj₂ z≤y₂ | inj₁ x≤z  = antisym (trans z≤y y≤x) x≤z
  ... | inj₂ z≤y₂ | inj₂ z≤x₂ = refl

  identityˡ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
              ∀ {⊥} → Maximum _≤_ ⊥ → LeftIdentity _≈_ ⊥ min
  identityˡ refl antisym {⊥} top x with total ⊥ x
  ... | inj₁ ⊥≤x = antisym ⊥≤x (top x)
  ... | inj₂ x≤⊥ = refl

  identityʳ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
              ∀ {⊥} → Maximum _≤_ ⊥ → RightIdentity _≈_ ⊥ min
  identityʳ refl antisym {⊥} top x with total x ⊥
  ... | inj₁ x≤⊥ = refl
  ... | inj₂ ⊥≤x = antisym ⊥≤x (top x)

  identity : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
             ∀ {⊥} → Maximum _≤_ ⊥ → Identity _≈_ ⊥ min
  identity refl antisym max =
    (identityˡ refl antisym max , identityʳ refl antisym max)

  zeroˡ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
          ∀ {⊥} → Minimum _≤_ ⊥ → LeftZero _≈_ ⊥ min
  zeroˡ refl antisym {⊥} bot x with total ⊥ x
  ... | inj₁ ⊥≤x = refl
  ... | inj₂ x≤⊥ = antisym x≤⊥ (bot x)

  zeroʳ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
          ∀ {⊥} → Minimum _≤_ ⊥ → RightZero _≈_ ⊥ min
  zeroʳ refl antisym {⊥} bot x with total x ⊥
  ... | inj₁ x≤⊥ = antisym x≤⊥ (bot x)
  ... | inj₂ ⊥≤x = refl

  zero : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
         ∀ {⊥} → Minimum _≤_ ⊥ → Zero _≈_ ⊥ min
  zero refl antisym bot = (zeroˡ refl antisym bot , zeroʳ refl antisym bot)

  isSemigroup : IsPartialOrder _≈_ _≤_ →
                IsSemigroup _≈_ min
  isSemigroup ord = record
    { isEquivalence = isEquivalence
    ; assoc         = assoc Eq.refl trans antisym
    ; ∙-cong        = cong Eq.sym antisym ≤-resp-≈
    } where open IsPartialOrder ord

  isMonoid : IsPartialOrder _≈_ _≤_ → ∀ {⊥} → Maximum _≤_ ⊥ →
             IsMonoid _≈_ min ⊥
  isMonoid ord max = record
    { isSemigroup = isSemigroup ord
    ; identity    = identity Eq.refl antisym max
    } where open IsPartialOrder ord


----------------------------------------------------------------------------
-- Other properties

  min[x,y]≈y⇒y≤x : _≈_ ⇒ _≤_ → Symmetric _≈_ →
                   ∀ {x y} → min x y ≈ y → y ≤ x
  min[x,y]≈y⇒y≤x refl sym {x} {y} x⊓y≈y with total x y
  ... | inj₁ _   = refl (sym x⊓y≈y)
  ... | inj₂ y≤x = y≤x

  min[x,y]≈x⇒x≤y : _≈_ ⇒ _≤_ → Symmetric _≈_ →
                   ∀ {x y} → min x y ≈ x → x ≤ y
  min[x,y]≈x⇒x≤y refl sym {x} {y} x⊓y≈x with total x y
  ... | inj₁ x≤y = x≤y
  ... | inj₂ _   = refl (sym x⊓y≈x)
