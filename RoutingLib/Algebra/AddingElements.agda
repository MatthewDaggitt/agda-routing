open import Level using (_⊔_)
open import Algebra.FunctionProperties.Core using (Op₂)
open import Algebra.FunctionProperties hiding (Op₂)
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (Maybe; Eq; decSetoid)
open import Data.Product using (_,_)

open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Algebra.AddingElements {a} (A : Set a) where

  Aₑ : Set a
  Aₑ = Maybe A

  open import Data.Maybe using () renaming (nothing to e; just to val) public
  open import Data.Maybe using () renaming (nothing to eEq; just to valEq) public

  module BiIdentity (_⊕_ : Op₂ A) where

    infix 6 _⊕ₑ_

    _⊕ₑ_ : Op₂ Aₑ
    e      ⊕ₑ v     = v
    v      ⊕ₑ e     = v
    val v  ⊕ₑ val w = val (v ⊕ w)

    ⊕ₑ-comm : ∀ {ℓ} {_≈_ : Rel A ℓ} → Reflexive _≈_ → Commutative _≈_ _⊕_ → Commutative (Eq _≈_) _⊕ₑ_
    ⊕ₑ-comm refl comm e       e       = Eq.nothing
    ⊕ₑ-comm refl comm (val v) e       = Eq.just refl
    ⊕ₑ-comm refl comm e       (val w) = Eq.just refl
    ⊕ₑ-comm refl comm (val v) (val w) = Eq.just (comm v w)

    ⊕ₑ-sel : ∀ {ℓ} {_≈_ : Rel A ℓ} → Reflexive _≈_ → Selective _≈_ _⊕_ → Selective (Eq _≈_) _⊕ₑ_
    ⊕ₑ-sel refl sel e       e       = inj₁ Eq.nothing
    ⊕ₑ-sel refl sel (val v) e       = inj₁ (Eq.just refl)
    ⊕ₑ-sel refl sel e       (val w) = inj₂ (Eq.just refl)
    ⊕ₑ-sel refl sel (val v) (val w) with sel v w
    ... | inj₁ v⊕w≈v = inj₁ (val v⊕w≈v)
    ... | inj₂ v⊕w≈w = inj₂ (val v⊕w≈w)

    ⊕ₑ-assoc : ∀ {ℓ} {_≈_ : Rel A ℓ} → Reflexive _≈_ → Associative _≈_ _⊕_ → Associative (Eq _≈_) _⊕ₑ_
    ⊕ₑ-assoc refl assoc e       e       e       = Eq.nothing
    ⊕ₑ-assoc refl assoc e       e       (val w) = Eq.just refl
    ⊕ₑ-assoc refl assoc e       (val v) e       = Eq.just refl
    ⊕ₑ-assoc refl assoc e       (val v) (val w) = Eq.just refl
    ⊕ₑ-assoc refl assoc (val u) e       e       = Eq.just refl
    ⊕ₑ-assoc refl assoc (val u) e       (val w) = Eq.just refl
    ⊕ₑ-assoc refl assoc (val u) (val v) e       = Eq.just refl
    ⊕ₑ-assoc refl assoc (val u) (val v) (val w) = Eq.just (assoc u v w)

    e-idₗ-⊕ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → Reflexive _≈_ → LeftIdentity (Eq _≈_) e _⊕ₑ_
    e-idₗ-⊕ₑ refl e       = Eq.nothing
    e-idₗ-⊕ₑ refl (val v) = Eq.just refl

    e-idᵣ-⊕ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → Reflexive _≈_ → RightIdentity (Eq _≈_) e _⊕ₑ_
    e-idᵣ-⊕ₑ refl {e}      = Eq.nothing
    e-idᵣ-⊕ₑ refl {val v}  = Eq.just refl

    e-id-⊕ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → Reflexive _≈_ → Identity (Eq _≈_) e _⊕ₑ_
    e-id-⊕ₑ refl = e-idₗ-⊕ₑ refl , e-idᵣ-⊕ₑ refl

    ⊕ₑ-pres-≈ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → Congruent₂ _≈_ _⊕_ → Congruent₂ (Eq _≈_) _⊕ₑ_
    ⊕ₑ-pres-≈ₑ resp Eq.nothing    Eq.nothing    = Eq.nothing
    ⊕ₑ-pres-≈ₑ pres Eq.nothing    (Eq.just w≈x) = Eq.just w≈x
    ⊕ₑ-pres-≈ₑ pres (Eq.just u≈v) Eq.nothing    = Eq.just u≈v
    ⊕ₑ-pres-≈ₑ pres (Eq.just u≈v) (Eq.just w≈x) = Eq.just (pres u≈v w≈x)



  module BiZero  (_⊕_ : Op₂ A) where

    infix 6 _⊕ₑ_

    _⊕ₑ_ : Op₂ Aₑ
    e ⊕ₑ v       = e
    v       ⊕ₑ e = e
    val v  ⊕ₑ val w  = val (v ⊕ w)

    ⊕ₑ-comm : ∀ {ℓ} {_≈_ : Rel A ℓ} → Commutative _≈_ _⊕_ → Commutative (Eq _≈_) _⊕ₑ_
    ⊕ₑ-comm comm e       e       = Eq.nothing
    ⊕ₑ-comm comm (val v) e       = Eq.nothing
    ⊕ₑ-comm comm e       (val w) = e
    ⊕ₑ-comm comm (val v) (val w) = val (comm v w)

    ⊕ₑ-sel : ∀ {ℓ} {_≈_ : Rel A ℓ} → Selective _≈_ _⊕_ → Selective (Eq _≈_) _⊕ₑ_
    ⊕ₑ-sel sel e       e       = inj₁ Eq.nothing
    ⊕ₑ-sel sel (val v) e       = inj₂ Eq.nothing
    ⊕ₑ-sel sel e       (val w) = inj₁ Eq.nothing
    ⊕ₑ-sel sel (val v) (val w) with sel v w
    ... | inj₁ v⊕w≈v = inj₁ (Eq.just v⊕w≈v)
    ... | inj₂ v⊕w≈w = inj₂ (Eq.just v⊕w≈w)

    ⊕ₑ-assoc : ∀ {ℓ} {_≈_ : Rel A ℓ} → Associative _≈_ _⊕_ → Associative (Eq _≈_) _⊕ₑ_
    ⊕ₑ-assoc assoc e       e       e       = Eq.nothing
    ⊕ₑ-assoc assoc e       e       (val w) = Eq.nothing
    ⊕ₑ-assoc assoc e       (val v) e       = Eq.nothing
    ⊕ₑ-assoc assoc e       (val v) (val w) = Eq.nothing
    ⊕ₑ-assoc assoc (val u) e    e          = Eq.nothing
    ⊕ₑ-assoc assoc (val u) e    (val w)    = Eq.nothing
    ⊕ₑ-assoc assoc (val u) (val v) e       = Eq.nothing
    ⊕ₑ-assoc assoc (val u) (val v) (val w) = Eq.just (assoc u v w)

    e-zeₗ-⊕ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → LeftZero (Eq _≈_) e _⊕ₑ_
    e-zeₗ-⊕ₑ e       = Eq.nothing
    e-zeₗ-⊕ₑ (val v) = Eq.nothing

    e-zeᵣ-⊕ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → RightZero (Eq _≈_) e _⊕ₑ_
    e-zeᵣ-⊕ₑ e       = Eq.nothing
    e-zeᵣ-⊕ₑ (val v) = Eq.nothing

    e-ze-⊕ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → Zero (Eq _≈_) e _⊕ₑ_
    e-ze-⊕ₑ = e-zeₗ-⊕ₑ , e-zeᵣ-⊕ₑ

    ⊕ₑ-pres-≈ₑ : ∀ {ℓ} {_≈_ : Rel A ℓ} → Congruent₂ _≈_ _⊕_ → Congruent₂ (Eq _≈_) _⊕ₑ_
    ⊕ₑ-pres-≈ₑ _    Eq.nothing    Eq.nothing    = Eq.nothing
    ⊕ₑ-pres-≈ₑ _    Eq.nothing    (Eq.just w≈x) = Eq.nothing
    ⊕ₑ-pres-≈ₑ _    (Eq.just u≈v) e             = Eq.nothing
    ⊕ₑ-pres-≈ₑ pres (Eq.just u≈v) (Eq.just w≈x) = Eq.just (pres u≈v w≈x)
