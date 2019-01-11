open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Function using (flip)
open import Relation.Binary.Lattice using (Minimum; Maximum)
import Relation.Binary.Construct.Converse as Converse

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Relation.Binary
import RoutingLib.Algebra.Construct.NaturalChoice.Min as Min

module RoutingLib.Algebra.Construct.NaturalChoice.Max
  {a ℓ} {A : Set a} {_≤_ : Rel A ℓ} (≤-total : Total _≤_) where

private

  total : Total (flip _≤_)
  total = Converse.total _≤_ ≤-total

  antisymᶠ : ∀ {ℓ₂} {_≈_ : Rel A ℓ₂} → Antisymmetric _≈_ _≤_ → Antisymmetric _≈_ (flip _≤_)
  antisymᶠ antisym = Converse.antisym _≤_ antisym

max : Op₂ A
max = Min.min total

----------------------------------------------------------------------------
-- Algebraic properties

module _ {ℓ₂} (_≈_ : Rel A ℓ₂) where

  sel : Reflexive _≈_ → Selective _≈_ max
  sel refl = Min.sel total _≈_ refl

module _ {ℓ₂} {_≈_ : Rel A ℓ₂} where

  cong : Symmetric _≈_ → Antisymmetric _≈_ _≤_ → _≤_ Respects₂ _≈_ → Congruent₂ _≈_ max
  cong sym antisym resp = Min.cong total sym (antisymᶠ antisym) (Converse.resp₂ _ _ resp)

  comm : Reflexive _≈_ →  Antisymmetric _≈_ _≤_ → Commutative _≈_ max
  comm refl antisym = Min.comm total refl (antisymᶠ antisym)

  assoc : Reflexive _≈_ → Transitive _≤_ → Antisymmetric _≈_ _≤_ → Associative _≈_ max
  assoc refl trans antisym = Min.assoc total refl (Converse.trans _≤_ trans) (antisymᶠ antisym)

  identityˡ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
              ∀ {⊥} → Minimum _≤_ ⊥ → LeftIdentity _≈_ ⊥ max
  identityˡ refl antisym min = Min.identityˡ total refl (antisymᶠ antisym) min

  identityʳ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
              ∀ {⊥} → Minimum _≤_ ⊥ → RightIdentity _≈_ ⊥ max
  identityʳ refl antisym min = Min.identityʳ total refl (antisymᶠ antisym) min

  identity : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
             ∀ {⊥} → Minimum _≤_ ⊥ → Identity _≈_ ⊥ max
  identity refl antisym min = Min.identity total refl (antisymᶠ antisym) min

  zeroˡ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
          ∀ {⊥} → Maximum _≤_ ⊥ → LeftZero _≈_ ⊥ max
  zeroˡ refl antisym max = Min.zeroˡ total refl (antisymᶠ antisym) max

  zeroʳ : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
        ∀ {⊥} → Maximum _≤_ ⊥ → RightZero _≈_ ⊥ max
  zeroʳ refl antisym max = Min.zeroʳ total refl (antisymᶠ antisym) max

  zero : Reflexive _≈_ → Antisymmetric _≈_ _≤_ →
         ∀ {⊥} → Maximum _≤_ ⊥ → Zero _≈_ ⊥ max
  zero refl antisym max = Min.zero total refl (antisymᶠ antisym) max

  isSemigroup : IsPartialOrder _≈_ _≤_ →
                IsSemigroup _≈_ max
  isSemigroup ord = Min.isSemigroup total (Converse.isPartialOrder ord)

  isMonoid : IsPartialOrder _≈_ _≤_ → ∀ {⊥} → Minimum _≤_ ⊥ →
             IsMonoid _≈_ max ⊥
  isMonoid ord min = Min.isMonoid total (Converse.isPartialOrder ord) min

----------------------------------------------------------------------------
-- Other properties

  max[x,y]≈y⇒x≤y : _≈_ ⇒ _≤_ → Symmetric _≈_ →
                    ∀ {x y} → max x y ≈ y → x ≤ y
  max[x,y]≈y⇒x≤y refl sym = Min.min[x,y]≈y⇒y≤x total (Converse.reflexive _≤_ sym refl) sym
    
  max[x,y]≈x⇒y≤x : _≈_ ⇒ _≤_ → Symmetric _≈_ →
                   ∀ {x y} → max x y ≈ x → y ≤ x
  max[x,y]≈x⇒y≤x refl sym = Min.min[x,y]≈x⇒x≤y total (Converse.reflexive _≤_ sym refl) sym
