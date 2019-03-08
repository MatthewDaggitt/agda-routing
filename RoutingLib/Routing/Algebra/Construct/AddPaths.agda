--------------------------------------------------------------------------------
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
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; _,_)
open import Data.Product.Relation.Pointwise.NonDependent as Pointwise
  using (Pointwise)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary
open import Data.Product
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using ()
open import RoutingLib.Algebra.Construct.Lexicographic as Lex using (Lex)
open import RoutingLib.Algebra.Construct.Lexicographic.Magma as OpLexProperties′
open import RoutingLib.Function
open import RoutingLib.Relation.Nullary.Construct.Add.Point
  renaming (∙ to invalid; [_] to valid)
open import RoutingLib.Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq) using (∙≈∙; [_];[≈]-injective;≈∙-refl; ≈∙-sym)
open import RoutingLib.Data.Path.Uncertified renaming (_∈ₚ_ to _∈ᴱ_; _∉ₚ_ to _∉̂ᴱ_; Path to EPath; _⇿_ to _⇿ᴱ_)
open import RoutingLib.Data.Path.Uncertified.Choice
open import RoutingLib.Data.Path.Uncertified.Properties 
open import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder
open import RoutingLib.Data.Path.UncertifiedI 

------------------------------------------------------------------------
-- Prelude

private
  ≈ₓ-refl : Reflexive (Pointwise {A₂ = EPath} _≈_ _≡_)
  ≈ₓ-refl = Pointwise.×-refl {_∼₁_ = _≈_} {_≡_} ≈-refl refl
  
  module LexProperties = OpLexProperties′ ⊕-decMagma ⊓ₗₑₓ-magma

------------------------------------------------------------------------
-- Definition



infix 4 _≈⁺_ _≉⁺_
infix 7 _⊕⁺_
infix 6 _▷⁺_

Route⁺ : Set a
Route⁺ = Pointed (Route × EPath)

Step⁺ : ∀ {n} → Fin n → Fin n → Set b
Step⁺ i j = Step i j

_≈⁺_ : Rel Route⁺ ℓ
_≈⁺_ = PointedEq (Pointwise _≈_ _≡_)

≈⁺-refl : Reflexive _≈⁺_
≈⁺-refl = ≈∙-refl (Pointwise _≈_ _≡_) ( Pointwise.×-refl {_∼₁_ = _≈_} {_∼₂_ = _≡_} ≈-refl  refl ) 


≈⁺-sym : Symmetric _≈⁺_
≈⁺-sym = ≈∙-sym (Pointwise _≈_ _≡_) ( Pointwise.×-symmetric {_∼₁_ = _≈_} {_∼₂_ = _≡_} ≈-sym sym ) 

_≉⁺_ : Rel Route⁺ ℓ
x ≉⁺ y = ¬ (x ≈⁺ y)

_⊕⁺_ : Op₂ Route⁺
_⊕⁺_ = AddIdentity (Lex _≟_ _⊕_ _⊓ₗₑₓ_)

_▷⁺_ : ∀ {n} {i j : Fin n} → Step⁺ i j → Route⁺ → Route⁺
_▷⁺_ {_} {i} {j} f invalid         = invalid
_▷⁺_ {_} {i} {j} f (valid (x , p))
  with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  _ | _     | _     = invalid
... | yes _ | yes _ | _     = invalid
... | yes _ | no  _ | yes _ = invalid
... | yes _ | no  _ | no  _ = valid (f ▷ x , (toℕ i , toℕ j) ∷ p)

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
⊕⁺-cong = AddIdentity.⊕∙-cong _ ≈ₓ-refl LexProperties.cong

▷⁺-cong : ∀ {n} {i j : Fin n} (f : Step i j) → Congruent₁ _≈⁺_ (f ▷⁺_)
▷⁺-cong {_} {i} {j} f {_}             {_}             ∙≈∙     = ∙≈∙
▷⁺-cong {_} {i} {j} f {valid (x , p)} {valid (y , p)} [ x≈y , refl ]
  with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞# | f ▷ y ≟ ∞#
... | no  _ | _     | _         | _          = ∙≈∙
... | yes _ | yes _ | _         | _          = ∙≈∙
... | yes _ | no  _ | yes _     | yes _      = ∙≈∙
... | yes _ | no  _ | yes f▷x≈∞ | no  f▷y≉∞ = contradiction (≈-trans (▷-cong f (≈-sym x≈y)) f▷x≈∞) f▷y≉∞
... | yes _ | no  _ | no  f▷x≉∞ | yes f▷y≈∞ = contradiction (≈-trans (▷-cong f x≈y) f▷y≈∞) f▷x≉∞
... | yes _ | no  _ | no  _     | no  _     = [ ▷-cong f x≈y , refl ]

f∞⁺-reject : ∀ {n} (i j : Fin n) (x : Route⁺) → f∞⁺ i j ▷⁺ x ≈⁺ ∞#⁺
f∞⁺-reject i j invalid         = ∙≈∙
f∞⁺-reject i j (valid (x , p)) with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f∞ i j ▷ x ≟ ∞#
... | no  _ | _     | _          = ∙≈∙
... | yes _ | yes _ | _          = ∙≈∙
... | yes _ | no  _ | yes _      = ∙≈∙
... | yes _ | no  _ | no  f∞▷x≉∞ = contradiction (f∞-reject i j x) f∞▷x≉∞

AddPaths : RawRoutingAlgebra a b ℓ
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
  renaming ( ≤₊-respˡ-≈ to  ≤₊⁺-respˡ-≈⁺; ≤₊-respʳ-≈ to  ≤₊⁺-respʳ-≈⁺)

--------------------------------------------------------------------------------
-- Adding paths preserves the required properties of a routing algebra

⊕⁺-sel : Selective _≈_ _⊕_ → Selective _≈⁺_ _⊕⁺_
⊕⁺-sel ⊕-sel = AddIdentity.⊕∙-sel _ ≈ₓ-refl (LexProperties.sel ⊕-sel ⊓ₗₑₓ-sel)

⊕⁺-comm : Commutative _≈_ _⊕_ → Commutative _≈⁺_ _⊕⁺_
⊕⁺-comm ⊕-comm = AddIdentity.⊕∙-comm _ ≈ₓ-refl (LexProperties.comm ⊕-comm ⊓ₗₑₓ-comm)

⊕⁺-assoc : Associative _≈_ _⊕_ → Associative _≈⁺_ _⊕⁺_
⊕⁺-assoc ⊕-assoc = AddIdentity.⊕∙-assoc _ ≈ₓ-refl (LexProperties.assoc ⊕-assoc ⊓ₗₑₓ-assoc)

⊕⁺-zeroʳ : RightZero _≈_ 0# _⊕_ → RightZero _≈⁺_ 0#⁺ _⊕⁺_
⊕⁺-zeroʳ ⊕-zeroʳ = AddIdentity.⊕∙-zeroʳ _ ≈ₓ-refl (LexProperties.zeroʳ ⊕-zeroʳ ⊓ₗₑₓ-zeroʳ)

⊕⁺-identityʳ : RightIdentity _≈⁺_ ∞#⁺ _⊕⁺_
⊕⁺-identityʳ = AddIdentity.⊕∙-identityʳ _ ≈ₓ-refl

▷⁺-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷⁺ ∞#⁺ ≈⁺ ∞#⁺
▷⁺-fixedPoint f = ∙≈∙

isRoutingAlgebra : IsRoutingAlgebra A → IsRoutingAlgebra AddPaths
isRoutingAlgebra A-isRoutingAlgebra = record
  { ⊕-sel        = ⊕⁺-sel ⊕-sel
  ; ⊕-comm       = ⊕⁺-comm ⊕-comm
  ; ⊕-assoc      = ⊕⁺-assoc ⊕-assoc
  ; ⊕-zeroʳ       = ⊕⁺-zeroʳ ⊕-zeroʳ
  ; ⊕-identityʳ   = ⊕⁺-identityʳ
  ; ▷-fixedPoint = ▷⁺-fixedPoint
  }
  where open IsRoutingAlgebra A-isRoutingAlgebra

--------------------------------------------------------------------------------
-- Other properties


-- some of this could be more general and moved to Lex file.
G : Route  → Route  → EPath  → EPath → EPath
G x y p q with (x ⊕ y) ≟ x | (x ⊕ y) ≟ y
... | yes _ | no  _ = p
... | no  _ | yes _ = q
... | _     | _     = p ⊓ₗₑₓ q

private
  _≈ₓ_ : Rel (Route × EPath) _
  _≈ₓ_ = (Pointwise _≈_ _≡_)
  _⊕ₗ_   = (Lex _≟_ _⊕_ _⊓ₗₑₓ_)

-- G (bad name) allows us to reason equationally rather than using case analysis .. 
Lex-G : ∀ {x y p q} → ((x , p) ⊕ₗ (y , q)) ≈ₓ (x ⊕ y , G x y p q)
Lex-G {x} {y} {p} {q} with  x ⊕ y ≟ x | x ⊕ y ≟ y
Lex-G {x} {y} {p} {q} | yes p₁ | yes p₂ = ≈-refl , refl
Lex-G {x} {y} {p} {q} | yes p₁ | no ¬p = (≈-sym p₁) ,  refl
Lex-G {x} {y} {p} {q} | no ¬p | yes p₁ = (≈-sym p₁) ,  refl
Lex-G {x} {y} {p} {q} | no ¬p | no ¬p₁ = ≈-refl , refl

Lex-G⁺ : ∀ x y p q → (valid (x , p)) ⊕⁺ (valid (y , q)) ≈⁺ valid (x ⊕ y , G x y p q)
Lex-G⁺ x y p q =  [  Lex-G  ]

Lex-G-∉̂ᴱ : ∀ {n} {i : Fin n} x y p q (i∉p : toℕ i ∉̂ᴱ p) (i∉q : toℕ i ∉̂ᴱ q) → toℕ i ∉̂ᴱ (G x y p q)
Lex-G-∉̂ᴱ {n} {i} x y p q i∉p i∉q with x ⊕ y ≟ x  | x ⊕ y ≟ y | ⊓ₗₑₓ-sel p q
... | yes _ | yes _ | inj₁ x₁ = ∉ₚ-resp-≈ₚ (sym x₁) i∉p
... | yes _ | yes _ | inj₂ y₁ = ∉ₚ-resp-≈ₚ (sym y₁) i∉q
... | yes _ | no _  | _ = i∉p
... | no _  | yes _ | _ = i∉q
... | no _  | no _  | inj₁ x₁ = ∉ₚ-resp-≈ₚ (sym x₁) i∉p
... | no _  | no _  | inj₂ y₁ = ∉ₚ-resp-≈ₚ (sym y₁) i∉q


Lex-G-dist : ∀ {n} {i j : Fin n} x y p q →  (toℕ i , toℕ j) ∷ (G x y p q) ≡ (G x y ((toℕ i , toℕ j) ∷ p) ((toℕ i , toℕ j) ∷ q)) 
Lex-G-dist {n} {i} {j} x y p q with x ⊕ y ≟ x  | x ⊕ y ≟ y 
... | yes _ | yes _ = ∷-distrib-⊓ₗₑₓ (toℕ i , toℕ j) p q 
... | yes _ | no _  = refl 
... | no _  | yes _ = refl 
... | no _  | no _  = ∷-distrib-⊓ₗₑₓ (toℕ i , toℕ j) p q 



eql : ∀ {x} {y} {r} {s} → ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ (valid (x , r)) → (x ⊕ y) ≈ x
eql {x} {y} {r} {s} h with  x ⊕ y ≟ x | x ⊕ y ≟ y
eql {x} {y} {r} {s} h | yes p | _ = p
eql {x} {y} {r} {s} h | no _  | yes p = ≈-trans p (proj₁ ([≈]-injective _ h))
eql {x} {y} {r} {s} h | no ¬p | no ¬p₁ = contradiction (proj₁ ([≈]-injective _ h)) ¬p 

eqr : ∀ {x} {y} {r} {s} → ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ (valid (y , s)) → (x ⊕ y) ≈ y 
eqr {x} {y} {r} {s} h with  x ⊕ y ≟ x | x ⊕ y ≟ y
eqr {x} {y} {r} {s} h | _ | yes p  = p
eqr {x} {y} {r} {s} h | yes p | no _ = ≈-trans p (proj₁ ([≈]-injective _ h))
eqr {x} {y} {r} {s} h | no ¬p | no ¬p₁ = contradiction (proj₁ ([≈]-injective _ h)) ¬p₁

▷⁺-valid : ∀ {n} {i j : Fin n} (f : Step i j) x p (i∉p : toℕ i ∉̂ᴱ p) → ((toℕ i , toℕ j) ⇿ᵥ p) → (f ▷ x ≉ ∞#) → (f ▷⁺ (valid (x , p))) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ p) 
▷⁺-valid {n} {i} {j} f x p i∉p ij⇿p fx≉∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  ¬ij⇿p | _     | _         = contradiction ij⇿p ¬ij⇿p 
... | yes _ | yes i∈p | _       = contradiction i∈p i∉p
... | yes _ | no  _ | yes f▷x≈∞ = contradiction f▷x≈∞ fx≉∞
... | yes _ | no  _ | no  f▷x≉∞ = ≈⁺-refl 



▷⁺-reject : ∀ {n} {i j : Fin n} (f : Step i j) x p → f ▷ x ≈ ∞# → f ▷⁺ (valid (x , p)) ≈⁺ ∞#⁺
▷⁺-reject {_} {i} {j} f x p f▷x≈∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  _ | _     | _         = ∙≈∙
... | yes _ | yes _ | _         = ∙≈∙
... | yes _ | no  _ | yes _     = ∙≈∙
... | yes _ | no  _ | no  f▷x≉∞ = contradiction f▷x≈∞ f▷x≉∞

▷⁺-accept : ∀ {n} {i j : Fin n} (f : Step i j) x p →
            (toℕ i , toℕ j) ⇿ᴱ p → toℕ i ∉̂ᴱ p → f ▷ x ≉ ∞# →
            f ▷⁺ (valid (x , p)) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ p)
▷⁺-accept {_} {i} {j} f x p ij⇿p i∉p f▷x≉∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no ¬ij⇿p | _       | _         = contradiction ij⇿p ¬ij⇿p
... | yes _    | yes i∈p | _         = contradiction i∈p i∉p
... | yes _    | no  _   | yes f▷x≈∞ = contradiction f▷x≈∞ f▷x≉∞
... | yes _    | no  _   | no  _     = [ ≈-refl , refl ]


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
  with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  _    | _       | _           = ∙≈∙
... | yes _    | yes _   | _           = ∙≈∙
... | yes _    | no  _   | yes _       = ∙≈∙
... | yes ij⇿p | no  i∉p | no  f∞▷x≉∞ = Sum.[ contradiction ij⇿p , contradiction ◌ i∉p ] v

path⁺-accept : ∀ {n} {i j : Fin n} {r p} (f : Step⁺ i j) →
              path⁺ r ≡ valid p → f ▷⁺ r ≉⁺ ∞#⁺ →
              path⁺ (f ▷⁺ r) ≡ valid ((toℕ i , toℕ j) ∷ p)
path⁺-accept {i = i} {j} {invalid}       f _    f▷r≉∞ = contradiction ∙≈∙ f▷r≉∞
path⁺-accept {i = i} {j} {valid (x , p)} f refl f▷r≉∞
  with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  _    | _       | _           = contradiction ∙≈∙ f▷r≉∞
... | yes _    | yes _   | _           = contradiction ∙≈∙ f▷r≉∞
... | yes _    | no  _   | yes _       = contradiction ∙≈∙ f▷r≉∞
... | yes ij⇿p | no  i∉p | no  f∞▷x≉∞ = refl

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


--------------------------------------------------------------------------------
-- Properties preserved


open PathDistributivity isPathAlgebra

{-

  IsLevel_PathDistributiveIn[_,_] : ℕ → Route → Route → Set _
  IsLevel 0       PathDistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Fin n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    (toℕ i , toℕ j) ⇿ path x → (toℕ i , toℕ j) ⇿ path y →
    f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y) 

  IsLevel (suc k) PathDistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Fin n} (f : Step i j) 
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    IsLevel k PathDistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]

-}


cong-path-distrib : ∀ a b c d → a ≈⁺ c → b ≈⁺ d → ∀ k → IsLevel k PathDistributiveIn[ a , b ] → IsLevel k PathDistributiveIn[ c , d ]

cong-path-distrib a b c d a≈⁺c b≈⁺d zero dis[a,b] {n} {i} {j} f {x} {y} c≤₊x x≤₊d c≤₊y y≤₊d i∉ₚpathx i∉ₚpathy  ij⇿pathx ij⇿pathy =  cnc
  where
  cnc : f ▷⁺ (x ⊕⁺ y) ≈⁺  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)
  cnc =  dis[a,b] {n} {i} {j} f {x} {y}
    (≤₊⁺-respˡ-≈⁺ {x} (≈⁺-sym a≈⁺c) c≤₊x)
    (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) x≤₊d)
    (≤₊⁺-respˡ-≈⁺ {y}  (≈⁺-sym a≈⁺c) c≤₊y)
    (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) y≤₊d)
    i∉ₚpathx  i∉ₚpathy  ij⇿pathx ij⇿pathy 
  
cong-path-distrib a b c d a≈⁺c b≈⁺d (suc k) dis[a,b] {n} {i} {j} f {x} {y} c≤₊x x≤₊d c≤₊y y≤₊d i∉ₚpathx i∉ₚpathy  =  cnc
  where
  cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (x ⊕⁺ y) ,  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)  ]
  cnc =  dis[a,b] {n} {i} {j} f {x} {y}
    (≤₊⁺-respˡ-≈⁺ {x} (≈⁺-sym a≈⁺c) c≤₊x)
    (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) x≤₊d)
    (≤₊⁺-respˡ-≈⁺ {y}  (≈⁺-sym a≈⁺c) c≤₊y)
    (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) y≤₊d)
    i∉ₚpathx  i∉ₚpathy

  
{-  
cong-path-constant : ∀ k a b → a ≈⁺ b  → IsLevel k PathDistributiveIn[ a , b ]

cong-path-constant zero a b a≈⁺b {n} {i} {j} f {x} {y} a≤₊x x≤₊a b≤₊y y≤₊b i∉ₚpathx i∉ₚpathy  ij⇿pathx ij⇿pathy =  cnc
  where 
  cnc : f ▷⁺ (x ⊕⁺ y) ≈⁺  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)
  cnc = {!!}
  
cong-path-constant (suc k) a b a≈⁺b {n} {i} {j} f {x} {y} a≤₊x x≤₊a b≤₊y y≤₊b i∉ₚpathx i∉ₚpathy  =  cnc
  where
  x≈⁺a : x ≈⁺ a
  x≈⁺a = {!!} 

  y≈⁺b : y ≈⁺ b
  y≈⁺b = {!!} 

  x≈⁺y : x ≈⁺ y
  x≈⁺y = {!!}

  tst : f ▷⁺ (x ⊕⁺ y) ≈⁺ ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))  
  tst = {!!}  --- need idempotence, eq-reasoning over ≈⁺
  
  cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (x ⊕⁺ y) ,  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)  ]
  cnc =   cong-path-constant k (f ▷⁺ (x ⊕⁺ y)) ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))  tst   
  



module _ (⊕-sel : Selective _≈_ _⊕_) (⊕-identityˡ : LeftIdentity _≈_ ∞# _⊕_) where

{-
  
  open IsDecEquivalence ≈⁺-isDecEquivalence
    using () renaming (trans to ≈⁺-trans)

  private
    _≈ₓ_ : Rel (Route × EPath) _
    _≈ₓ_ = (Pointwise _≈_ _≡_)
    _⊕ₗ_   = (Lex _≟_ _⊕_ _⊓ₗₑₓ_)

  ⊕ˡ-sel : Selective _≈ₓ_ _⊕ₗ_
  ⊕ˡ-sel = Lex.sel {_≈₂_ = _≡_}  _≟_    _⊕_    _⊓ₗₑₓ_   ≈-refl   refl ⊕-sel ⊓ₗₑₓ-sel

  lemma1 : ∀ {⊤ ⊥} → Level_DistributiveIn[_,_] A 0 ⊥ ⊤ → 
           ∀ {n} {i j : Fin n} {f : Step i j} {x y p q} →
           ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
           f ▷ x ≈ ∞# → valid (x , p) ⊕⁺ valid (y , q) ≈⁺ valid (x , p) → f ▷ y ≈ ∞#
  lemma1 distrib {f = f} {x} {y} {p} {q} ⊥≤x x≤⊤ ⊥≤y y≤⊤ f▷x≈∞ xp⊕yq≈xp = begin
    f ▷ y             ≈⟨ ≈-sym (⊕-identityˡ (f ▷ y)) ⟩
    ∞# ⊕ (f ▷ y)      ≈⟨ ⊕-cong (≈-sym f▷x≈∞) ≈-refl ⟩
    (f ▷ x) ⊕ (f ▷ y) ≈⟨ ≈-sym (distrib f ⊥≤x x≤⊤ ⊥≤y y≤⊤) ⟩
    f ▷ (x ⊕ y)       ≈⟨ ▷-cong f lemma0 ⟩ 
    f ▷ x             ≈⟨ f▷x≈∞ ⟩
    ∞#                ∎
      where
      lemma_a : ((x , p) ⊕ₗ (y , q)) ≈ₓ (x , p)
      lemma_a = [≈]-injective  _≈ₓ_ xp⊕yq≈xp

      lemma_b : (proj₁ (x , p)) ⊕ (proj₁ (y , q)) ≈ proj₁ ((x , p) ⊕ₗ (y , q)) 
      lemma_b =  ≈-sym (Lex.opLex-proj₁ {_≈₂_ =  _≡_}  _≟_  _⊕_  _⊓ₗₑₓ_  ≈-refl  ≈-sym   (x , p)  (y , q))

      lemma0 : x ⊕ y ≈ x
      lemma0 = begin 
                (x ⊕ y)                             ≈⟨  ⊕-cong  ≈-refl ≈-refl ⟩
                ((proj₁ (x , p)) ⊕ (proj₁ (y , q))) ≈⟨  lemma_b ⟩                
                proj₁ ((x , p) ⊕ₗ (y , q))          ≈⟨ {!!} ⟩                
                proj₁ (x , p)                       ≈⟨  ≈-refl ⟩                
                x                                   ∎

-}

  -- needed? 
  path⁺-valid : ∀ {p x}  → path⁺ (valid (x , p)) ≡ valid p
  path⁺-valid = refl
  
  ∉ₚto∉̂ᴱ : ∀ {n x p} {i : Fin n}  → (toℕ i) ∉ₚ (path⁺ (valid (x , p))) → toℕ i ∉̂ᴱ p
  ∉ₚto∉̂ᴱ i∉ₚ = λ z → i∉ₚ (valid z) 

  pres-distrib : ∀ {k ⊤ ⊥} → Level_DistributiveIn[_,_] A k ⊥ ⊤ →
                 ∀ p q → IsLevel_PathDistributiveIn[_,_] k (valid (⊥ , p)) (valid (⊤ , q))
  pres-distrib {zero} {⊤} {⊥} dist p q {n} {i} {j} f {invalid}       {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _    = ∙≈∙
  pres-distrib {zero} {⊤} {⊥} dist p q {n} {i} {j} f {valid (x , r)} {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _
    with (toℕ i , toℕ j) ⇿? r  | toℕ i ∈ₚ? r | f ▷ x ≟ ∞#
  ... | no  _    | _       | _           = ∙≈∙
  ... | yes _    | yes _   | _           = ∙≈∙
  ... | yes _    | no  _   | yes _       = ∙≈∙
  ... | yes ij⇿p | no  i∉p | no  f∞▷x≉∞  = [ ≈-refl , refl ]
  pres-distrib {zero} {⊤} {⊥} dist p q {_} {i} {j} f {invalid}       {valid (y , s)} ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _
    with (toℕ i , toℕ j) ⇿? s  | toℕ i ∈ₚ? s | f ▷ y ≟ ∞#
  ... | no  _    | _       | _           = ∙≈∙
  ... | yes _    | yes _   | _           = ∙≈∙
  ... | yes _    | no  _   | yes _       = ∙≈∙
  ... | yes ij⇿p | no  i∉p | no  f∞▷x≉∞  = [ ≈-refl , refl ]
  pres-distrib {zero} {⊤} {⊥} dist p q {n} {i} {j} f {valid (x , r)} {valid (y , s)} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s (just ij⇿r) (just ij⇿s) =  cnc
     where
     
     dst : f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y)
     dst = dist f (eqr ⊥≤x) (eqr x≤⊤)  (eqr ⊥≤y) (eqr y≤⊤)

     -- needed? 
     lm_a :  (f ▷⁺ (valid (x , r))) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ r)
     lm_a =  ▷⁺-valid f x r (∉ₚto∉̂ᴱ {_} {x} {r} {i} i∉r)

     -- needed? 
     lm_b :  (f ▷⁺ (valid (y , s))) ≈⁺ valid (f ▷ y , (toℕ i , toℕ j) ∷ s)
     lm_b =  ▷⁺-valid f y s (∉ₚto∉̂ᴱ {_} {x} {s} {i} i∉s)

     cnc : f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ ((f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))))
     cnc = begin 
           f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s)))                                              ≈⟨  ▷⁺-cong f ((Lex-G⁺ x y r s)) ⟩
           f ▷⁺ (valid (x ⊕ y , G x y r s))                                                       ≈⟨  ▷⁺-valid f _ _ (Lex-G-∉̂ᴱ  x  y  r s ( (∉ₚto∉̂ᴱ {n} {x} {r} {i} i∉r) ) ( (∉ₚto∉̂ᴱ {n} {y}  {s} {i} i∉s)))  ⟩ 
           valid (f ▷ (x ⊕ y) , (toℕ i , toℕ j)  ∷  (G x y r s))                               ≈⟨ {!!} ⟩ -- cong and dst
           valid ((f ▷ x) ⊕ (f ▷ y) , (toℕ i , toℕ j) ∷ (G x y r s))                           ≈⟨ {!!} ⟩ -- cong and Lex-G-dist
           valid ((f ▷ x) ⊕ (f ▷ y) ,  (G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s))) ≈⟨ {!!} ⟩ -- cong, sym, and Lex-G⁺
           valid (f ▷ x , (toℕ i , toℕ j) ∷ r) ⊕⁺ valid (f ▷ y , (toℕ i , toℕ j) ∷ s)       ≈⟨ ⊕⁺-cong (≈⁺-sym (▷⁺-valid f x r  (∉ₚto∉̂ᴱ {n} {x} {r} {i} i∉r)))  ≈⁺-refl  ⟩
           (f ▷⁺ (valid (x , r))) ⊕⁺ valid (f ▷ y , (toℕ i , toℕ j) ∷ s)                        ≈⟨ ⊕⁺-cong  ≈⁺-refl (≈⁺-sym (▷⁺-valid f y s  ( (∉ₚto∉̂ᴱ {n} {y} {s} {i} i∉s)))) ⟩
           (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s)))                                     ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })  -- HERE 

  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {invalid}       {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _     = cnc
    where
--  cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (invalid ⊕⁺ invalid) , (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ invalid) ]
    cnc : IsLevel k PathDistributiveIn[ invalid , invalid ]
    cnc = cong-path-constant k invalid invalid  ≈⁺-refl 
    
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r _ = cnc 
    where

    tst : f ▷⁺ ((valid (x , r)) ⊕⁺ invalid) ≈⁺ (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ invalid)
    tst  = begin
           f ▷⁺ ((valid (x , r)) ⊕⁺ invalid)      ≈⟨   ▷⁺-cong f ( ⊕⁺-cong  ≈⁺-refl  {!!})  ⟩
           (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ invalid) ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })
           

    cnc : IsLevel k PathDistributiveIn[ f ▷⁺ ((valid (x , r)) ⊕⁺ invalid) , (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ invalid) ]
    cnc = cong-path-constant k _ _ tst

  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {invalid} {valid (y , s)}        ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ i∉s = cnc 
    where

    tst : f ▷⁺ (invalid ⊕⁺ (valid (y , s)) ) ≈⁺ (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ (valid (y , s)))
    tst = begin
           f ▷⁺ (invalid ⊕⁺ (valid (y , s)) )      ≈⟨   {!!}  ⟩
           f ▷⁺ (valid (y , s))                    ≈⟨   {!!}  ⟩
           invalid ⊕⁺ (f ▷⁺ (valid (y , s)))       ≈⟨   {!!}  ⟩                     
           (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ (valid (y , s))) ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })
    
    cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (invalid ⊕⁺ (valid (y , s)) ) , (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ (valid (y , s))) ]    
    cnc = cong-path-constant k _ _ tst
    
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {valid (y , s)}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s = cnc 
    where
    dst : Level_DistributiveIn[_,_] A k (f ▷ (x ⊕ y)) ((f ▷ x) ⊕ (f ▷ y)) 
    dst = dist f (eqr ⊥≤x) (eqr x≤⊤)  (eqr ⊥≤y) (eqr y≤⊤)

    tst : IsLevel k PathDistributiveIn[   valid ( f ▷ (x ⊕ y) , (toℕ i , toℕ j) ∷ (G x y r s)) ,
                                          valid ( ((f ▷ x) ⊕ (f ▷ y)) , G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s) )
                                      ]    
    tst = pres-distrib {k} {((f ▷ x) ⊕ (f ▷ y)) }
                       {(f ▷ (x ⊕ y))} dst
                       ((toℕ i , toℕ j) ∷ (G x y r s))
                       (G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s))

    eq1 : valid ( f ▷ (x ⊕ y) , (toℕ i , toℕ j) ∷ (G x y r s))  ≈⁺ f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s)) ) 
    eq1 = {!!}

    eq2 : valid ( ((f ▷ x) ⊕ (f ▷ y)) , G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s) )
          ≈⁺
          (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s)))
    eq2 = {!!} 

    cnc : IsLevel k PathDistributiveIn[ f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s)) ) , (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))) ]    
    cnc =  cong-path-distrib _ _ _ _ eq1 eq2 k tst  
-}
