--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module turns a distance vector protocol into a path vector protocol by
-- adding a component that tracks and removes paths. Note that the choice and
-- extension operators of the original algebra cannot access the paths and
-- therefore this is not suitable for protocols which makes decisions based
-- on a path-weight's associated path.
--------------------------------------------------------------------------------

open import Algebra
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Maybe; just)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise using (Pointwise)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq)
  using (∙≈∙; [_]; [≈]-injective; ≈∙-refl; ≈∙-sym; ≈∙-trans)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction; contradiction₂)
open import Relation.Nullary.Construct.Add.Point renaming (∙ to invalid; [_] to valid)

open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using (⊕∙-comm)
open import RoutingLib.Routing.Basics.Path.Uncertified
  renaming (_∈ₚ_ to _∈ᴱ_; _∉ₚ_ to _∉ᴱ_; Path to EPath; _⇿_ to _⇿ᴱ_)
open import RoutingLib.Routing.Basics.Path.Uncertified.Choice
open import RoutingLib.Routing.Basics.Path.Uncertified.Properties

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Construct.AddPaths
  {a b ℓ} (A : RawRoutingAlgebra a b ℓ) where

open RawRoutingAlgebra A

open import Algebra.Construct.LexProduct ⊕-magma ⊓ₗₑₓ-magma _≟_ as Lex
  renaming (_⊕_ to lex)
  
------------------------------------------------------------------------
-- Prelude

_≈ₓ_ : Rel (PathWeight × EPath) _
_≈ₓ_ = (Pointwise _≈_ _≡_)

_⊕ₗₑₓ_ : Op₂ (PathWeight × EPath)
_⊕ₗₑₓ_  = lex

≈ₓ-refl : Reflexive (Pointwise {B = EPath} _≈_ _≡_)
≈ₓ-refl = Pointwise.×-refl {R = _≈_} {S = _≡_} ≈-refl refl

≈ₓ-cong : Congruent₂ _≈ₓ_ _⊕ₗₑₓ_
≈ₓ-cong = Lex.cong

------------------------------------------------------------------------
-- Definition

infix 4 _≈⁺_ _≉⁺_
infix 7 _⊕⁺_
infix 6 _▷⁺_

PathWeight⁺ : Set a
PathWeight⁺ = Pointed (PathWeight × EPath)

Step⁺ : ∀ {n} → Fin n → Fin n → Set b
Step⁺ i j = Step i j

_≈⁺_ : Rel PathWeight⁺ _
_≈⁺_ = PointedEq _≈ₓ_ 

≈⁺-refl : Reflexive _≈⁺_
≈⁺-refl = ≈∙-refl _≈ₓ_ ( Pointwise.×-refl {R = _≈_} {S = _≡_} ≈-refl  refl ) 

≈⁺-sym : Symmetric _≈⁺_
≈⁺-sym = ≈∙-sym _≈ₓ_ ( Pointwise.×-symmetric {R = _≈_} {S = _≡_} ≈-sym sym ) 

≈⁺-trans : Transitive _≈⁺_
≈⁺-trans = ≈∙-trans _≈ₓ_ ( Pointwise.×-transitive {R = _≈_} {S = _≡_} ≈-trans trans ) 

_≉⁺_ : Rel PathWeight⁺ _
x ≉⁺ y = ¬ (x ≈⁺ y)

_⊕⁺_ : Op₂ PathWeight⁺
_⊕⁺_ = AddIdentity _⊕ₗₑₓ_

_▷⁺_ : ∀ {n} {i j : Fin n} → Step⁺ i j → PathWeight⁺ → PathWeight⁺
_▷⁺_ {_} {i} {j} f invalid         = invalid
_▷⁺_ {_} {i} {j} f (valid (x , p))
  with  f ▷ x ≟ ∞#  | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
... | yes  _ | _     | _     = invalid
... |  _     | no  _ | _     = invalid
... |  _     | _     | yes _ = invalid  
... | no  _  | yes _ | no  _ = valid (f ▷ x , (toℕ i , toℕ j) ∷ p)

0#⁺ : PathWeight⁺
0#⁺ = valid (0# , [])

∞#⁺ : PathWeight⁺
∞#⁺ = invalid

f∞⁺ : ∀ {n} (i j : Fin n) → Step i j
f∞⁺ = f∞

≈⁺-isEquivalence : IsEquivalence _≈⁺_
≈⁺-isEquivalence = PointedEq.≈∙-isEquivalence (Pointwise _≈_ _≡_)
  (Pointwise.×-isEquivalence ≈-isEquivalence isEquivalence)

≈⁺-isDecEquivalence : IsDecEquivalence _≈⁺_
≈⁺-isDecEquivalence = PointedEq.≈∙-isDecEquivalence (Pointwise _≈_ _≡_)
  (Pointwise.×-isDecEquivalence ≈-isDecEquivalence ≡ₚ-isDecEquivalence)

⊕⁺-cong : Congruent₂ _≈⁺_ _⊕⁺_
⊕⁺-cong = AddIdentity.⊕∙-cong _ ≈ₓ-refl ≈ₓ-cong 

▷⁺-cong : ∀ {n} {i j : Fin n} (f : Step i j) → Congruent₁ _≈⁺_ (f ▷⁺_)
▷⁺-cong {_} {i} {j} f {_}             {_}             ∙≈∙     = ∙≈∙
▷⁺-cong {_} {i} {j} f {valid (x , p)} {valid (y , p)} [ x≈y , refl ]
  with f ▷ x ≟ ∞# | f ▷ y ≟ ∞# | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p 
... | yes _     | yes _      | _     | _     = ∙≈∙
... | yes f▷x≈∞ | no  f▷y≉∞  | _     | _     = contradiction (≈-trans (▷-cong f (≈-sym x≈y)) f▷x≈∞) f▷y≉∞
... | no f▷x≉∞  | yes f▷y≈∞  | _     | _     = contradiction (≈-trans (▷-cong f x≈y) f▷y≈∞) f▷x≉∞
... | no f▷x≉∞  | no  f▷y≉∞  | no _  | _     = ∙≈∙
... | no f▷x≉∞  | no  f▷y≉∞  | yes _ | yes _ = ∙≈∙
... | no f▷x≉∞  | no  f▷y≉∞  | yes _ | no _  = [ ▷-cong f x≈y , refl ]

f∞⁺-reject : ∀ {n} (i j : Fin n) (x : PathWeight⁺) → f∞⁺ i j ▷⁺ x ≈⁺ ∞#⁺
f∞⁺-reject i j invalid         = ∙≈∙
f∞⁺-reject i j (valid (x , p)) with f∞ i j ▷ x ≟ ∞# | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p 
... | yes _      | _     | _     = ∙≈∙
... | no  _      | no _  | _     = ∙≈∙
... | no  _      | yes _ | yes _ = ∙≈∙
... | no  f∞▷x≉∞ | yes _ | no  _ = contradiction (f∞-reject i j x) f∞▷x≉∞ 

AddPaths : RawRoutingAlgebra a b (a ⊔ ℓ)
AddPaths = record
  { PathWeight              = PathWeight⁺
  ; Step               = Step⁺
  ; _≈_                = _≈⁺_
  ; _⊕_                = _⊕⁺_
  ; _▷_                = _▷⁺_
  ; 0#                 = 0#⁺
  ; ∞#                 = ∞#⁺
  ; f∞                 = f∞⁺
  ; ≈-isDecEquivalence = ≈⁺-isDecEquivalence
  ; ⊕-cong             = ⊕⁺-cong
  ; ▷-cong             = ▷⁺-cong
  ; f∞-reject          = f∞⁺-reject
  }

open RawRoutingAlgebra AddPaths using ()
  renaming
  ( ≤₊-respˡ-≈ to ≤₊⁺-respˡ-≈⁺
  ; ≤₊-respʳ-≈ to  ≤₊⁺-respʳ-≈⁺
  ; _≤₊_ to _≤₊⁺_
  )

--------------------------------------------------------------------------------
-- Adding paths preserves the required properties of a routing algebra

module _ (A-isRoutingAlgebra : IsRoutingAlgebra A) where
  open IsRoutingAlgebra A-isRoutingAlgebra

  ⊕ₓ-sel : Selective _≈ₓ_ _⊕ₗₑₓ_
  ⊕ₓ-sel = Lex.sel ⊕-sel ⊓ₗₑₓ-sel

  ⊕ₓ-comm : Commutative _≈ₓ_ _⊕ₗₑₓ_
  ⊕ₓ-comm = Lex.comm ⊕-comm ⊓ₗₑₓ-comm

  ⊕ₓ-assoc : Associative _≈ₓ_ _⊕ₗₑₓ_
  ⊕ₓ-assoc = Lex.assoc ⊕-assoc ⊕-comm ⊕-sel ⊓ₗₑₓ-assoc 

  ⊕⁺-sel : Selective _≈⁺_ _⊕⁺_
  ⊕⁺-sel = AddIdentity.⊕∙-sel _ ≈ₓ-refl ⊕ₓ-sel 

  ⊕⁺-idem : Idempotent _≈⁺_ _⊕⁺_
  ⊕⁺-idem a with ⊕⁺-sel a a
  ⊕⁺-idem a | inj₁ x = x
  ⊕⁺-idem a | inj₂ y = y 

  ⊕⁺-comm : Commutative _≈⁺_ _⊕⁺_
  ⊕⁺-comm = AddIdentity.⊕∙-comm _ ≈ₓ-refl ⊕ₓ-comm

  ⊕⁺-assoc : Associative _≈⁺_ _⊕⁺_
  ⊕⁺-assoc = AddIdentity.⊕∙-assoc _ ≈ₓ-refl ⊕ₓ-assoc

  ⊕⁺-zeroʳ : RightZero _≈⁺_ 0#⁺ _⊕⁺_
  ⊕⁺-zeroʳ = AddIdentity.⊕∙-zeroʳ _ ≈ₓ-refl (Lex.zeroʳ ⊕-zeroʳ ⊓ₗₑₓ-zeroʳ)

  ⊕⁺-identityʳ : RightIdentity _≈⁺_ ∞#⁺ _⊕⁺_
  ⊕⁺-identityʳ = AddIdentity.⊕∙-identityʳ _ ≈ₓ-refl

  ▷⁺-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷⁺ ∞#⁺ ≈⁺ ∞#⁺
  ▷⁺-fixedPoint f = ∙≈∙

  isRoutingAlgebra : IsRoutingAlgebra AddPaths
  isRoutingAlgebra = record
    { ⊕-sel        = ⊕⁺-sel
    ; ⊕-comm       = ⊕⁺-comm 
    ; ⊕-assoc      = ⊕⁺-assoc
    ; ⊕-zeroʳ      = ⊕⁺-zeroʳ 
    ; ⊕-identityʳ  = ⊕⁺-identityʳ
    ; ▷-fixedPoint = ▷⁺-fixedPoint
    }

--------------------------------------------------------------------------------
-- The resulting algebra is a path algebra

path⁺ : PathWeight⁺ → Maybe EPath
path⁺ invalid         = invalid
path⁺ (valid (x , p)) = valid p

path⁺-cong : path⁺ Preserves _≈⁺_ ⟶ _≡_
path⁺-cong ∙≈∙          = refl
path⁺-cong [ _ , refl ] = refl

r≈0⇒path⁺[r]≈[] : ∀ {r} → r ≈⁺ 0#⁺ → path⁺ r ≡ valid []
r≈0⇒path⁺[r]≈[] [ _ , refl ] = refl
r≈∞⇒path⁺[r]≈∅ : ∀ {r} → r ≈⁺ ∞#⁺ → path⁺ r ≡ invalid
r≈∞⇒path⁺[r]≈∅ ∙≈∙ = refl

path⁺[r]≈∅⇒r≈∞ : ∀ {r} → path⁺ r ≡ invalid → r ≈⁺ ∞#⁺
path⁺[r]≈∅⇒r≈∞ {invalid} refl = ∙≈∙
path⁺[r]≈∅⇒r≈∞ {valid x} ()

path⁺-reject : ∀ {n} {i j : Fin n} {r p} (f : Step⁺ i j) →
            path⁺ r ≡ valid p → ¬ (toℕ i , toℕ j) ⇿ᴱ p ⊎ toℕ i ∈ᴱ p →
            f ▷⁺ r ≈⁺ ∞#⁺
path⁺-reject {i = i} {j} {invalid}       f _    v = ∙≈∙
path⁺-reject {i = i} {j} {valid (x , p)} f refl v 
  with f ▷ x ≟ ∞# | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p 
... | yes _ | _        | _       = ∙≈∙
... | no _  | no _     | _       = ∙≈∙
... | no _  | yes _    | yes _   = ∙≈∙
... | no _  | yes ij⇿p | no  i∉p = contradiction₂ v (λ r → r ij⇿p) i∉p

path⁺-accept : ∀ {n} {i j : Fin n} {r p} (f : Step⁺ i j) →
               path⁺ r ≡ valid p → f ▷⁺ r ≉⁺ ∞#⁺ →
               path⁺ (f ▷⁺ r) ≡ valid ((toℕ i , toℕ j) ∷ p)
path⁺-accept {i = i} {j} {invalid}       f _    f▷r≉∞ = contradiction ∙≈∙ f▷r≉∞
path⁺-accept {i = i} {j} {valid (x , p)} f refl f▷r≉∞ 
  with f ▷ x ≟ ∞# | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p 
... | yes  _    | _       | _     = contradiction ∙≈∙ f▷r≉∞
... | no _      | no _    | _     = contradiction ∙≈∙ f▷r≉∞
... | no _      | yes _   | yes _ = contradiction ∙≈∙ f▷r≉∞
... | no _      | yes _   | no  _ = refl 

isPathAlgebra : IsPathAlgebra AddPaths
isPathAlgebra = record
  { path           = path⁺
  ; path-cong      = path⁺-cong
  ; r≈0⇒path[r]≈[] = r≈0⇒path⁺[r]≈[]
  ; r≈∞⇒path[r]≈∅  = r≈∞⇒path⁺[r]≈∅
  ; path[r]≈∅⇒r≈∞  = path⁺[r]≈∅⇒r≈∞
  ; path-reject    = path⁺-reject
  ; path-accept    = path⁺-accept
  }

------------------
-- useful lemmas
------------------

⊕⁺invalidₗ : ∀ x  → (invalid ⊕⁺ x) ≈⁺ x
⊕⁺invalidₗ x =  ≈⁺-refl

⊕⁺invalidᵣ : ∀ x  → (x ⊕⁺ invalid) ≈⁺ x
⊕⁺invalidᵣ invalid =  ≈⁺-refl
⊕⁺invalidᵣ (valid(x , p)) = ≈⁺-refl 

⊕⁺-case₁ : ∀ {a b} x y  → (a ⊕ b) ≈ a → (a ⊕ b) ≉ b → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(a , x) 
⊕⁺-case₁ x y ab=a ¬ab=b = [ Lex.case₁ ab=a ¬ab=b x y ]

⊕⁺-case₁⁻¹ : ∀ {a b x y}  → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(a , x) → a ⊕ b ≈ a 
⊕⁺-case₁⁻¹ [ fst , _ ] = fst

⊕⁺-case₂ : ∀ {a b} x y  → (a ⊕ b) ≉ a → (a ⊕ b) ≈ b → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(b , y) 
⊕⁺-case₂ x y ¬ab=a ab=b = [ Lex.case₂ ¬ab=a ab=b x y ]

⊕⁺-case₂⁻¹ : ∀ {a b x y}  → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(b , y) → a ⊕ b ≈ b 
⊕⁺-case₂⁻¹ [ fst , _ ] = fst

⊕⁺-case₃ : ∀ {a b} x y  → (a ⊕ b) ≈ a → (a ⊕ b) ≈ b → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(a , x ⊓ₗₑₓ y) 
⊕⁺-case₃ x y ab=a ab=b = [ Lex.case₃ ab=a ab=b x y ]


≤₊⁺⇒≤⁺ : ∀ {x y p q} → valid (x , p) ≤₊⁺ valid (y , q) → x ≤₊ y
≤₊⁺⇒≤⁺ [ x⊕y≈x , _ ] = x⊕y≈x

▷⁺-accept : ∀ {n} {i j : Fin n} {f : Step⁺ i j} {x p} →
            f ▷ x ≉ ∞# → (toℕ i , toℕ j) ⇿ᴱ p → toℕ i ∉ᴱ p → 
            f ▷⁺ valid (x , p) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ p)
▷⁺-accept {n} {i} {j} {f} {x} {p} f▷x≉∞ ij⇿p i∉p with f ▷ x ≟ ∞# | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
... | yes f▷x≈∞ | _        | _       = contradiction f▷x≈∞ f▷x≉∞
... | no  _     | no ¬ij⇿p | _       = contradiction ij⇿p ¬ij⇿p
... | no  _     | yes _    | yes i∈p = contradiction i∈p i∉p
... | no  _     | yes _    | no  _   = [ ≈-refl , refl ]

▷⁺-reject-≈∞ : ∀ {n} {i j : Fin n} {f : Step⁺ i j} {x p} →
               f ▷ x ≈ ∞# → f ▷⁺ valid (x , p) ≈⁺ ∞#⁺
▷⁺-reject-≈∞ {n} {i} {j} {f} {x} {p} f▷x≈∞ with f ▷ x ≟ ∞#
... | yes _     = ∙≈∙
... | no  f▷x≉∞ = contradiction f▷x≈∞ f▷x≉∞
