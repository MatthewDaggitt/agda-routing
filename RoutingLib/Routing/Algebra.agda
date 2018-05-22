open import Algebra.FunctionProperties
open import Algebra.FunctionProperties.Consequences using (sel⇒idem)
open import Data.Fin using (Fin)
open import Data.List using (List)
import Data.List.Any.Membership as ListMembership
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Maybe
open import Data.Sum using (_⊎_)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
open import RoutingLib.Data.SimplePath
  using (SimplePath; valid; invalid; []; _∷_∣_∣_)
open import RoutingLib.Data.SimplePath.Relation.Equality
import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder
open import RoutingLib.Data.SimplePath
  using (SimplePath; []; _∷_∣_∣_; valid; invalid; length)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.NonEmpty using (_⇿_; _∈_)

module RoutingLib.Routing.Algebra  where

--------------------------------------------------------------------------------
-- Routing algebras --
--------------------------------------------------------------------------------
-- Routing algebra

record IsRoutingAlgebra
  {a b ℓ} {Route : Set a} {Step : Set b}
  (_≈_ : Rel Route ℓ)
  (_⊕_ : Op₂ Route)
  (_▷_ : Step → Route → Route)
  (0# ∞ : Route) : Set (a ⊔ b ⊔ ℓ)
  where
  
  field
    ≈-isDecEquivalence : IsDecEquivalence _≈_

    ⊕-cong             : Congruent₂    _≈_ _⊕_
    ⊕-sel              : Selective     _≈_ _⊕_
    ⊕-comm             : Commutative   _≈_ _⊕_
    ⊕-assoc            : Associative   _≈_ _⊕_
    ⊕-zeroʳ            : RightZero     _≈_ 0# _⊕_
    ⊕-identityʳ        : RightIdentity _≈_ ∞ _⊕_

    ▷-cong             : ∀ e → Congruent₁ _≈_ (e ▷_)
    ▷-zero             : ∀ (f : Step) → (f ▷ ∞) ≈ ∞

  open IsDecEquivalence ≈-isDecEquivalence public
    renaming
    ( refl          to ≈-refl
    ; reflexive     to ≈-reflexive
    ; sym           to ≈-sym
    ; trans         to ≈-trans
    ; isEquivalence to ≈-isEquivalence
    ) public

  infix 4 _≉_
  _≉_ : Rel Route ℓ
  x ≉ y = ¬ (x ≈ y)
  
  open RightNaturalOrder _≈_ _⊕_ public
    using () renaming
    ( _≤_ to _≤₊_
    ; _≰_ to _≰₊_
    ; _<_ to _<₊_
    )

  S : Setoid a ℓ
  S = record { isEquivalence = ≈-isEquivalence }

  DS : DecSetoid a ℓ
  DS = record { isDecEquivalence = ≈-isDecEquivalence }

record RoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_

  field
    Step             : Set a
    Route            : Set b
    _≈_              : Rel Route ℓ
    _⊕_              : Op₂ Route
    _▷_              : Step → Route → Route
    0#               : Route
    ∞                : Route
    isRoutingAlgebra : IsRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

  open IsRoutingAlgebra isRoutingAlgebra public

--------------------------------------------------------------------------------
-- Increasing routing algebras

record IsIncreasingRoutingAlgebra
  {a b ℓ} {Route : Set a} {Step : Set b}
  (_≈_ : Rel Route ℓ)
  (_⊕_ : Op₂ Route) (_▷_ : Step → Route → Route)
  (0# ∞ : Route) : Set (a ⊔ b ⊔ ℓ)
  where
  
  field
    isRoutingAlgebra     : IsRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

  open IsRoutingAlgebra isRoutingAlgebra public

  field
    ▷-increasing : ∀ f x → x ≤₊ (f ▷ x) 

record IncreasingRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_
  
  field
    Step  : Set a
    Route : Set b
    _≈_   : Rel Route ℓ
    _⊕_   : Op₂ Route
    _▷_   : Step → Route → Route
    0#    : Route
    ∞     : Route
    isIncreasingRoutingAlgebra : IsIncreasingRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

  open IsIncreasingRoutingAlgebra isIncreasingRoutingAlgebra public
  
  routingAlgebra : RoutingAlgebra a b ℓ
  routingAlgebra = record {isRoutingAlgebra = isRoutingAlgebra}

--------------------------------------------------------------------------------
-- Strictly increasing routing algebras

record IsStrictlyIncreasingRoutingAlgebra
  {a b ℓ} {Route : Set a} {Step : Set b}
  (_≈_ : Rel Route ℓ)
  (_⊕_ : Op₂ Route) (_▷_ : Step → Route → Route)
  (0# ∞ : Route) : Set (a ⊔ b ⊔ ℓ)
  where
  
  field
    isRoutingAlgebra     : IsRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

  open IsRoutingAlgebra isRoutingAlgebra public

  field
    ▷-strictlyIncreasing : ∀ f {x} → x ≉ ∞ → x <₊ (f ▷ x) 

  ▷-increasing : ∀ f x → x ≤₊ f ▷ x
  ▷-increasing f x with x ≟ ∞
  ... | no  x≉∞ = proj₁ (▷-strictlyIncreasing f x≉∞)
  ... | yes x≈∞ = begin
    (f ▷ x) ⊕ x ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
    (f ▷ ∞) ⊕ ∞ ≈⟨ ⊕-cong (▷-zero f) ≈-refl ⟩
    ∞       ⊕ ∞ ≈⟨ sel⇒idem S ⊕-sel ∞ ⟩
    ∞           ≈⟨ ≈-sym x≈∞ ⟩
    x           ∎
    where open EqReasoning S

  isIncreasingRoutingAlgebra : IsIncreasingRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞
  isIncreasingRoutingAlgebra = record
    { isRoutingAlgebra = isRoutingAlgebra
    ; ▷-increasing     = ▷-increasing
    }

record StrictlyIncreasingRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_
  
  field
    Step  : Set a
    Route : Set b
    _≈_   : Rel Route ℓ
    _⊕_   : Op₂ Route
    _▷_   : Step → Route → Route
    0#    : Route
    ∞     : Route
    isStrictlyIncreasingRoutingAlgebra : IsStrictlyIncreasingRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

  open IsStrictlyIncreasingRoutingAlgebra isStrictlyIncreasingRoutingAlgebra public
  
  routingAlgebra : RoutingAlgebra a b ℓ
  routingAlgebra = record {isRoutingAlgebra = isRoutingAlgebra}

  increasingRoutingAlgebra : IncreasingRoutingAlgebra a b ℓ
  increasingRoutingAlgebra = record
    { isIncreasingRoutingAlgebra = isIncreasingRoutingAlgebra
    }
  
--------------------------------------------------------------------------------
-- Increasing path algebra

record IsFiniteStrictlyIncreasingRoutingAlgebra
  {a b ℓ} {Route : Set a} {Step : Set b}
  (_≈_ : Rel Route ℓ)
  (_⊕_ : Op₂ Route) (_▷_ : Step → Route → Route)
  (0# ∞ : Route) : Set (a ⊔ b ⊔ ℓ)
  where

  field
    isStrictlyIncreasingRoutingAlgebra : IsStrictlyIncreasingRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

  open IsStrictlyIncreasingRoutingAlgebra isStrictlyIncreasingRoutingAlgebra public
  open ListMembership S renaming (_∈_ to _∈ₗ_)

  field
    allRoutes   : List Route
    ∈-allRoutes : ∀ r → r ∈ₗ allRoutes

record FiniteStrictlyIncreasingRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_
  
  field
    Step  : Set a
    Route : Set b
    _≈_   : Rel Route ℓ
    _⊕_   : Op₂ Route
    _▷_   : Step → Route → Route
    0#    : Route
    ∞     : Route
    isFiniteStrictlyIncreasingRoutingAlgebra : IsFiniteStrictlyIncreasingRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

  open IsFiniteStrictlyIncreasingRoutingAlgebra isFiniteStrictlyIncreasingRoutingAlgebra public
  
  strictlyIncreasingRoutingAlgebra : StrictlyIncreasingRoutingAlgebra a b ℓ
  strictlyIncreasingRoutingAlgebra = record
    { isStrictlyIncreasingRoutingAlgebra = isStrictlyIncreasingRoutingAlgebra
    }

  open StrictlyIncreasingRoutingAlgebra strictlyIncreasingRoutingAlgebra public
    using (increasingRoutingAlgebra; routingAlgebra)


--------------------------------------------------------------------------------
-- Path algebras --
--------------------------------------------------------------------------------
-- Path algebra

record IsPathAlgebra
  {a b ℓ n} {Route : Set a} {Step : Set b}
  (_≈_ : Rel Route ℓ)
  (_⊕_ : Op₂ Route) (_▷_ : Step → Route → Route)
  (0# ∞ : Route)
  (A : SquareMatrix Step n)
  (path : Route → SimplePath n) : Set (a ⊔ b ⊔ ℓ)
  where

  field
    isRoutingAlgebra : IsRoutingAlgebra _≈_ _⊕_ _▷_ 0# ∞

    path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
    r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≈ₚ valid [] 
    r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞ → path r ≈ₚ invalid
    path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≈ₚ invalid  → r ≈ ∞
    path-reject    : ∀ {i j r p} → path r ≈ₚ valid p → ¬ (i , j) ⇿ p ⊎ i ∈ p →
                     (A i j ▷ r) ≈ ∞
    path-accept    : ∀ {i j r p} → path r ≈ₚ valid p → ¬ ((A i j ▷ r) ≈ ∞) →
                       ∀ ij⇿p i∉p → path (A i j ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

  open IsRoutingAlgebra isRoutingAlgebra public

  -- Functions
  
  size : Route → ℕ
  size r = length (path r)

  weight : SimplePath n → Route
  weight invalid                       = ∞
  weight (valid [])                    = 0#
  weight (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight (valid p)
  
  -- Consistency
  
  𝑪 : Route → Set ℓ
  𝑪 r = weight (path r) ≈ r

  𝑰 : Route → Set ℓ
  𝑰 r = ¬ 𝑪 r
  
record PathAlgebra a b ℓ n : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_
  
  field
    Step  : Set a
    Route : Set b
    _≈_   : Rel Route ℓ
    _⊕_   : Op₂ Route
    _▷_   : Step → Route → Route
    0#    : Route
    ∞     : Route
    A     : SquareMatrix Step n
    path  : Route → SimplePath n

    isPathAlgebra : IsPathAlgebra _≈_ _⊕_ _▷_ 0# ∞ A path

  open IsPathAlgebra isPathAlgebra public

  routingAlgebra : RoutingAlgebra a b ℓ
  routingAlgebra = record
    { isRoutingAlgebra = isRoutingAlgebra
    }


    
--------------------------------------------------------------------------------
-- Increasing path algebra

record IsIncreasingPathAlgebra
  {a b ℓ n} {Route : Set a} {Step : Set b}
  (_≈_ : Rel Route ℓ)
  (_⊕_ : Op₂ Route) (_▷_ : Step → Route → Route)
  (0# ∞ : Route)
  (A : SquareMatrix Step n)
  (path : Route → SimplePath n) : Set (a ⊔ b ⊔ ℓ)
  where

  field
    isPathAlgebra : IsPathAlgebra _≈_ _⊕_ _▷_ 0# ∞ A path

  open IsPathAlgebra isPathAlgebra public

  field
    ▷-increasing : ∀ f x → x ≤₊ (f ▷ x)

record IncreasingPathAlgebra a b ℓ n : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_
  
  field
    Step  : Set a
    Route : Set b
    _≈_   : Rel Route ℓ
    _⊕_   : Op₂ Route
    _▷_   : Step → Route → Route
    0#    : Route
    ∞     : Route
    A     : SquareMatrix Step n
    path  : Route → SimplePath n

    isIncreasingPathAlgebra : IsIncreasingPathAlgebra _≈_ _⊕_ _▷_ 0# ∞ A path

  open IsIncreasingPathAlgebra isIncreasingPathAlgebra public

  pathAlgebra : PathAlgebra a b ℓ n
  pathAlgebra = record
    { isPathAlgebra = isPathAlgebra
    }

  open PathAlgebra pathAlgebra public
    using (routingAlgebra)

--------------------------------------------------------------------------------
-- Strictly increasing path algebra

record IsStrictlyIncreasingPathAlgebra
  {a b ℓ n} {Route : Set a} {Step : Set b}
  (_≈_ : Rel Route ℓ)
  (_⊕_ : Op₂ Route) (_▷_ : Step → Route → Route)
  (0# ∞ : Route)
  (A : SquareMatrix Step n)
  (path : Route → SimplePath n) : Set (a ⊔ b ⊔ ℓ)
  where

  field
    isPathAlgebra : IsPathAlgebra _≈_ _⊕_ _▷_ 0# ∞ A path

  open IsPathAlgebra isPathAlgebra public

  field
    ▷-strictlyIncreasing : ∀ f {x} → x ≉ ∞ → x <₊ (f ▷ x)

  ▷-increasing : ∀ f x → x ≤₊ f ▷ x
  ▷-increasing f x with x ≟ ∞
  ... | no  x≉∞ = proj₁ (▷-strictlyIncreasing f x≉∞)
  ... | yes x≈∞ = begin
    (f ▷ x) ⊕ x ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
    (f ▷ ∞) ⊕ ∞ ≈⟨ ⊕-cong (▷-zero f) ≈-refl ⟩
    ∞       ⊕ ∞ ≈⟨ sel⇒idem S ⊕-sel ∞ ⟩
    ∞           ≈⟨ ≈-sym x≈∞ ⟩
    x           ∎
    where open EqReasoning S

  isIncreasingPathAlgebra : IsIncreasingPathAlgebra _≈_ _⊕_ _▷_ 0# ∞ A path
  isIncreasingPathAlgebra = record
    { isPathAlgebra = isPathAlgebra
    ; ▷-increasing     = ▷-increasing
    }
    
record StrictlyIncreasingPathAlgebra a b ℓ n : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_
  
  field
    Step  : Set a
    Route : Set b
    _≈_   : Rel Route ℓ
    _⊕_   : Op₂ Route
    _▷_   : Step → Route → Route
    0#    : Route
    ∞     : Route
    A     : SquareMatrix Step n
    path  : Route → SimplePath n

    isStrictlyIncreasingPathAlgebra : IsStrictlyIncreasingPathAlgebra _≈_ _⊕_ _▷_ 0# ∞ A path

  open IsStrictlyIncreasingPathAlgebra isStrictlyIncreasingPathAlgebra public

  increasingPathAlgebra : IncreasingPathAlgebra a b ℓ n
  increasingPathAlgebra = record
    { isIncreasingPathAlgebra = isIncreasingPathAlgebra
    }

  open IncreasingPathAlgebra increasingPathAlgebra public
    using (pathAlgebra; routingAlgebra)
