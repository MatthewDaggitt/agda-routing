--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module turns a distance vector protocol into a path vector protocol by
-- adding a component that tracks and removes paths. Note that the choice and
-- extension operators of the original algebra cannot access the paths and
-- therefore this is not suitable for protocols which makes decisions based
-- on a route's associated path.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Construct.AddPaths
  {a b ℓ} (A : RawRoutingAlgebra a b ℓ) where

open RawRoutingAlgebra A

open import Algebra.FunctionProperties
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Maybe; just)
open import Data.Product.Relation.Pointwise.NonDependent as Pointwise using (Pointwise)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq)
  using (∙≈∙; [_]; [≈]-injective; ≈∙-refl; ≈∙-sym; ≈∙-trans)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Construct.Add.Point renaming (∙ to invalid; [_] to valid)

open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using (⊕∙-comm)
open import RoutingLib.Algebra.Construct.Lexicographic as Lex using (Lex; Lex₂; Lex-case-1;Lex-case-2;Lex-case-3)
open import RoutingLib.Algebra.Construct.Lexicographic.Magma as OpLexProperties′
open import RoutingLib.Data.Path.Uncertified renaming (_∈ₚ_ to _∈ᴱ_; _∉ₚ_ to _∉̂ᴱ_; Path to EPath; _⇿_ to _⇿ᴱ_)
open import RoutingLib.Data.Path.Uncertified.Choice
open import RoutingLib.Data.Path.Uncertified.Properties
open import Relation.Binary.PropositionalEquality using (_≡_;isEquivalence)

------------------------------------------------------------------------
-- Prelude

module _ (⊕-assoc : Associative _≈_ _⊕_) (⊕-sel : Selective _≈_ _⊕_) (⊕-comm : Commutative _≈_ _⊕_)
  where

  module LexProperties = OpLexProperties′ ⊕-decMagma ⊓ₗₑₓ-magma

  _≈ₓ_ : Rel (Route × EPath) _
  _≈ₓ_ = (Pointwise _≈_ _≡_)

  _⊕ₗ_   = Lex _≟_ _⊕_ _⊓ₗₑₓ_
  G     = Lex₂ _≟_ _⊕_ _⊓ₗₑₓ_

  ⊕ₓ-sel : Selective (Pointwise _≈_ _≡_) (Lex _≟_ _⊕_ _⊓ₗₑₓ_)
  ⊕ₓ-sel = LexProperties.sel ⊕-sel ⊓ₗₑₓ-sel

  ≈ₓ-refl : Reflexive (Pointwise {A₂ = EPath} _≈_ _≡_)
  ≈ₓ-refl = Pointwise.×-refl {_∼₁_ = _≈_} {_≡_} ≈-refl refl

  ≈ₓ-cong : Congruent₂ (Pointwise _≈_ _≡_) (Lex _≟_ _⊕_ _⊓ₗₑₓ_)
  ≈ₓ-cong = LexProperties.cong

  ⊕ₓ-comm : Commutative (Pointwise _≈_ _≡_) (Lex _≟_ _⊕_ _⊓ₗₑₓ_)
  ⊕ₓ-comm = LexProperties.comm ⊕-comm ⊓ₗₑₓ-comm

  ⊕ₓ-assoc : Associative (Pointwise _≈_ _≡_) (Lex _≟_ _⊕_ _⊓ₗₑₓ_)
  ⊕ₓ-assoc = LexProperties.assoc ⊕-assoc ⊓ₗₑₓ-assoc ⊕-sel ⊕-comm 


------------------------------------------------------------------------
-- Definition

  infix 4 _≈⁺_ _≉⁺_
  infix 7 _⊕⁺_
  infix 6 _▷⁺_

  Route⁺ : Set a
  Route⁺ = Pointed (Route × EPath)

  Step⁺ : ∀ {n} → Fin n → Fin n → Set b
  Step⁺ i j = Step i j

  _≈⁺_ : Rel Route⁺ _
  _≈⁺_ = PointedEq _≈ₓ_ 

  ≈⁺-refl : Reflexive _≈⁺_
  ≈⁺-refl = ≈∙-refl _≈ₓ_ ( Pointwise.×-refl {_∼₁_ = _≈_} {_∼₂_ = _≡_} ≈-refl  refl ) 

  ≈⁺-sym : Symmetric _≈⁺_
  ≈⁺-sym = ≈∙-sym _≈ₓ_ ( Pointwise.×-symmetric {_∼₁_ = _≈_} {_∼₂_ = _≡_} ≈-sym sym ) 

  ≈⁺-trans : Transitive _≈⁺_
  ≈⁺-trans = ≈∙-trans _≈ₓ_ ( Pointwise.×-transitive {_∼₁_ = _≈_} {_∼₂_ = _≡_} ≈-trans trans ) 

  _≉⁺_ : Rel Route⁺ _
  x ≉⁺ y = ¬ (x ≈⁺ y)

  _⊕⁺_ : Op₂ Route⁺
  _⊕⁺_ = AddIdentity _⊕ₗ_   


  _▷⁺_ : ∀ {n} {i j : Fin n} → Step⁺ i j → Route⁺ → Route⁺
  _▷⁺_ {_} {i} {j} f invalid         = invalid
  _▷⁺_ {_} {i} {j} f (valid (x , p))
    with  f ▷ x ≟ ∞#  | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p
  ... | yes  _ | _     | _     = invalid
  ... |  _     | no  _ | _     = invalid
  ... |  _     | _     | yes _ = invalid  
  ... | no  _  | yes _ | no  _ = valid (f ▷ x , (toℕ i , toℕ j) ∷ p)

  0#⁺ : Route⁺
  0#⁺ = valid (0# , [])

  ∞#⁺ : Route⁺
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


  f∞⁺-reject : ∀ {n} (i j : Fin n) (x : Route⁺) → f∞⁺ i j ▷⁺ x ≈⁺ ∞#⁺
  f∞⁺-reject i j invalid         = ∙≈∙
  f∞⁺-reject i j (valid (x , p)) with f∞ i j ▷ x ≟ ∞# | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p 
  ... | yes _     | _     | _     = ∙≈∙
  ... | no _      | no _  | _     = ∙≈∙
  ... | no _      | yes _ | yes _ = ∙≈∙
  ... | no f∞▷x≉∞  | yes _ | no _  = contradiction (f∞-reject i j x) f∞▷x≉∞ 

  AddPaths : RawRoutingAlgebra a b (a ⊔ ℓ)
  AddPaths = record
    { Route              = Route⁺
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
    renaming ( ≤₊-respˡ-≈ to  ≤₊⁺-respˡ-≈⁺; ≤₊-respʳ-≈ to  ≤₊⁺-respʳ-≈⁺; _≤₊_ to _≤₊⁺_)

--------------------------------------------------------------------------------
-- Adding paths preserves the required properties of a routing algebra

  ⊕⁺-sel : Selective _≈⁺_ _⊕⁺_
  ⊕⁺-sel = AddIdentity.⊕∙-sel _ ≈ₓ-refl ⊕ₓ-sel 

  ⊕⁺-idem : Idempotent _≈⁺_ _⊕⁺_
  ⊕⁺-idem a with ⊕⁺-sel a a
  ⊕⁺-idem a | inj₁ x = x
  ⊕⁺-idem a | inj₂ y = y 

  ⊕⁺-comm : Commutative _≈⁺_ _⊕⁺_
  ⊕⁺-comm = AddIdentity.⊕∙-comm _ ≈ₓ-refl ⊕ₓ-comm


  ⊕⁺-assoc : Associative _≈_ _⊕_ → Associative _≈⁺_ _⊕⁺_
  ⊕⁺-assoc ⊕-assoc = AddIdentity.⊕∙-assoc _ ≈ₓ-refl ⊕ₓ-assoc

  ⊕⁺-zeroʳ : RightZero _≈_ 0# _⊕_ → RightZero _≈⁺_ 0#⁺ _⊕⁺_
  ⊕⁺-zeroʳ ⊕-zeroʳ = AddIdentity.⊕∙-zeroʳ _ ≈ₓ-refl (LexProperties.zeroʳ ⊕-zeroʳ ⊓ₗₑₓ-zeroʳ)

  ⊕⁺-identityʳ : RightIdentity _≈⁺_ ∞#⁺ _⊕⁺_
  ⊕⁺-identityʳ = AddIdentity.⊕∙-identityʳ _ ≈ₓ-refl

  ▷⁺-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷⁺ ∞#⁺ ≈⁺ ∞#⁺
  ▷⁺-fixedPoint f = ∙≈∙

  isRoutingAlgebra : IsRoutingAlgebra A → IsRoutingAlgebra AddPaths
  isRoutingAlgebra A-isRoutingAlgebra = record
    { ⊕-sel        = ⊕⁺-sel 
    ; ⊕-comm       = ⊕⁺-comm 
    ; ⊕-assoc      = ⊕⁺-assoc A-assoc
    ; ⊕-zeroʳ       = ⊕⁺-zeroʳ  ⊕-zeroʳ 
    ; ⊕-identityʳ   = ⊕⁺-identityʳ
    ; ▷-fixedPoint = ▷⁺-fixedPoint
    }
    where open IsRoutingAlgebra A-isRoutingAlgebra renaming (⊕-sel to A-sel; ⊕-comm to A-comm; ⊕-assoc to A-assoc)




--------------------------------------------------------------------------------
-- The resulting algebra is a path algebra

  path⁺ : Route⁺ → Maybe EPath
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
  ... | yes _ | _ | _ = ∙≈∙
  ... | no _  | no _ | _ = ∙≈∙
  ... | no _  | yes _ | yes _ = ∙≈∙
  ... | no _  | yes ij⇿p | no  i∉p = Sum.[ contradiction ij⇿p ,  (λ i∈p → contradiction i∈p i∉p) ] v  

  path⁺-accept : ∀ {n} {i j : Fin n} {r p} (f : Step⁺ i j) →
              path⁺ r ≡ valid p → f ▷⁺ r ≉⁺ ∞#⁺ →
              path⁺ (f ▷⁺ r) ≡ valid ((toℕ i , toℕ j) ∷ p)
  path⁺-accept {i = i} {j} {invalid}       f _    f▷r≉∞ = contradiction ∙≈∙ f▷r≉∞
  path⁺-accept {i = i} {j} {valid (x , p)} f refl f▷r≉∞ 
    with f ▷ x ≟ ∞# | (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p 
  ... | yes  _    | _       | _           = contradiction ∙≈∙ f▷r≉∞
  ... | no _      | no _    | _ = contradiction ∙≈∙ f▷r≉∞
  ... | no _      | yes _   | yes _ = contradiction ∙≈∙ f▷r≉∞
  ... | no _      | yes _   | no _ = refl 


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

  ⊕⁺-case-1 : ∀ {a b} x y  → (a ⊕ b) ≈ a → (a ⊕ b) ≉ b → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(a , x) 
  ⊕⁺-case-1 {a} {b} x y ab=a ¬ab=b = [ Lex-case-1 {_≈₁_ = _≈_}  {_≈₂_ = _≡_} ≈-isDecEquivalence isEquivalence  _⊕_  _⊓ₗₑₓ_ ⊕-cong  ⊓-cong  x y ab=a ¬ab=b  ]

  ⊕⁺-case-2 : ∀ {a b} x y  → (a ⊕ b) ≉ a → (a ⊕ b) ≈ b → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(b , y) 
  ⊕⁺-case-2 {a} {b} x y ¬ab=a ab=b = [ Lex-case-2 {_≈₁_ = _≈_}  {_≈₂_ = _≡_} ≈-isDecEquivalence isEquivalence  _⊕_  _⊓ₗₑₓ_ ⊕-cong  ⊓-cong  x y ¬ab=a ab=b  ]

  ⊕⁺-case-3 : ∀ {a b} x y  → (a ⊕ b) ≈ a → (a ⊕ b) ≈ b → valid(a , x) ⊕⁺ valid(b , y) ≈⁺ valid(a , x ⊓ₗₑₓ y) 
  ⊕⁺-case-3 {a} {b} x y ab=a ab=b = [ Lex-case-3 {_≈₁_ = _≈_}  {_≈₂_ = _≡_} ≈-isDecEquivalence isEquivalence  _⊕_  _⊓ₗₑₓ_ ⊕-cong  ⊓-cong  x y ab=a ab=b  ]


