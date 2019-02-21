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

module RoutingLib.Algebra.Construct.Add.Zero {a} (A : Set a) (_⊕_ : Op₂ A) where

Aₑ : Set a
Aₑ = Maybe A

open import Data.Maybe using () renaming (nothing to e;   just to val) public
open import Data.Maybe using () renaming (nothing to eEq; just to valEq) public

infix 6 _⊕ₑ_

_⊕ₑ_ : Op₂ Aₑ
e      ⊕ₑ v       = e
v      ⊕ₑ e = e
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
