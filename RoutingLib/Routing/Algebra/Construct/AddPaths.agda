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
--open import Relation.Binary.EqReasoning S
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using ()
open import RoutingLib.Algebra.Construct.Lexicographic as Lex using (Lex)
open import RoutingLib.Function
open import RoutingLib.Relation.Nullary.Construct.Add.Point
  renaming (∙ to invalid; [_] to valid)
open import RoutingLib.Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq) using (∙≈∙; [_];[≈]-injective)
open import RoutingLib.Data.Path.Uncertified renaming (_∈ₚ_ to _∈ᴱ_; _∉ₚ_ to _∉̂ᴱ_; Path to EPath; _⇿_ to _⇿ᴱ_)
open import RoutingLib.Data.Path.Uncertified.Choice
open import RoutingLib.Data.Path.Uncertified.Properties 
open import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder
open import RoutingLib.Data.Path.UncertifiedI 

infix 4 _≈⁺_ _≉⁺_
infix 7 _⊕⁺_
infix 6 _▷⁺_

Route⁺ : Set a
Route⁺ = Pointed (Route × EPath)

Step⁺ : ∀ {n} → Fin n → Fin n → Set b
Step⁺ i j = Step i j

_≈⁺_ : Rel Route⁺ ℓ
_≈⁺_ = PointedEq (Pointwise _≈_ _≡_)

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

private
  ≈ₓ-refl : Reflexive (Pointwise {A₂ = EPath} _≈_ _≡_)
  ≈ₓ-refl = Pointwise.×-refl {_∼₁_ = _≈_} {_≡_} ≈-refl refl

≈⁺-isDecEquivalence : IsDecEquivalence _≈⁺_
≈⁺-isDecEquivalence = PointedEq.≈∙-isDecEquivalence (Pointwise _≈_ _≡_)
  (Pointwise.×-isDecEquivalence ≈-isDecEquivalence ≡ₚ-isDecEquivalence)

⊕⁺-cong : Congruent₂ _≈⁺_ _⊕⁺_
⊕⁺-cong = AddIdentity.⊕∙-cong _ ≈ₓ-refl
  (Lex.cong _≟_ _⊕_ _⊓ₗₑₓ_ ≈-sym ≈-trans ⊕-cong (cong₂ _⊓ₗₑₓ_))

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


--------------------------------------------------------------------------------
-- Adding paths preserves the required properties of a routing algebra

⊕⁺-sel : Selective _≈_ _⊕_ → Selective _≈⁺_ _⊕⁺_
⊕⁺-sel ⊕-sel = AddIdentity.⊕∙-sel _ ≈ₓ-refl
  (Lex.sel {_≈₂_ = _≡_} _≟_ _⊕_ _⊓ₗₑₓ_ ≈-refl (refl {A = EPath}) ⊕-sel ⊓ₗₑₓ-sel)

⊕⁺-comm : Commutative _≈_ _⊕_ → Commutative _≈⁺_ _⊕⁺_
⊕⁺-comm ⊕-comm = AddIdentity.⊕∙-comm _ ≈ₓ-refl
  (Lex.comm {_≈₂_ = _≡_} _≟_ _⊕_ _⊓ₗₑₓ_ ≈-refl refl ≈-trans ⊕-comm ⊓ₗₑₓ-comm)

⊕⁺-assoc : Associative _≈_ _⊕_ → Associative _≈⁺_ _⊕⁺_
⊕⁺-assoc ⊕-assoc = AddIdentity.⊕∙-assoc _ ≈ₓ-refl
  (Lex.assoc {_≈₂_ = _≡_} _≟_ _⊕_ _⊓ₗₑₓ_ ≈-refl refl ≈-trans ⊕-assoc ⊓ₗₑₓ-assoc)

⊕⁺-zeroʳ : RightZero _≈_ 0# _⊕_ → RightZero _≈⁺_ 0#⁺ _⊕⁺_
⊕⁺-zeroʳ ⊕-zeroʳ = AddIdentity.⊕∙-zeroʳ _ ≈ₓ-refl
  (Lex.zeroʳ {_≈₂_ = _≡_} _≟_ _⊕_ _⊓ₗₑₓ_ ≈-refl refl ⊕-zeroʳ ⊓ₗₑₓ-zeroʳ)

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

eql : ∀ {x} {y} {r} {s} → ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ (valid (x , r)) → (x ⊕ y) ≈ x
eql = {!!} 

eqr : ∀ {x} {y} {r} {s} → ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ (valid (y , s)) → (x ⊕ y) ≈ y 
eqr = {!!}

▷⁺-valid : ∀ {n} {i j : Fin n} (f : Step i j) x p (i∉p : toℕ i ∉̂ᴱ p) → (f ▷⁺ (valid (x , p))) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ p)
▷⁺-valid = {!!}


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
... | yes _    | no  xxx   | yes f▷x≈∞ = contradiction f▷x≈∞ f▷x≉∞
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
  pres-distrib {zero} {⊤} {⊥} dist p q {_} {i} {j} f {invalid}       {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _    = ∙≈∙
  pres-distrib {zero} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _
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
  pres-distrib {zero} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {valid (y , s)} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s (just ij⇿r) (just ij⇿s) =  cnc
     where
     
     dst : f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y)
     dst = dist f (eqr ⊥≤x) (eqr x≤⊤)  (eqr ⊥≤y) (eqr y≤⊤)

     -- needed? 
     lm_a :  (f ▷⁺ (valid (x , r))) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ r)
     lm_a =  ▷⁺-valid f x r (∉ₚto∉̂ᴱ {_} {x} {r} {i} i∉r)

     -- needed? 
     lm_b :  (f ▷⁺ (valid (y , s))) ≈⁺ valid (f ▷ y , (toℕ i , toℕ j) ∷ s)
     lm_b =  ▷⁺-valid f y s (∉ₚto∉̂ᴱ {_} {x} {s} {i} i∉s)

     private
      _≈ₓ_ : Rel (Route × EPath) _
      _≈ₓ_ = (Pointwise _≈_ _≡_)
      _⊕ₗ_   = (Lex _≟_ _⊕_ _⊓ₗₑₓ_)

     -- some of this could be more general and moved to Lex file. 
     G : Route  → Route  → EPath  → EPath → EPath
     G x y p q with (x ⊕ y) ≟ x | (x ⊕ y) ≟ y
     ... | yes _ | no  _ = p
     ... | no  _ | yes _ = q
     ... | _     | _     = p ⊓ₗₑₓ q

     -- G (bad name) allows us to reason equationally rather than using case analysis .. 
     Lex-G : ∀ {x y p q} → ((x , p) ⊕ₗ (y , q)) ≈ₓ (x ⊕ y , G x y p q)
     Lex-G = {! !}

     Lex-G⁺ : ∀ {x y p q} → (valid (x , r)) ⊕⁺ (valid (y , s)) ≈⁺ valid (x ⊕ y , G x y p q)
     Lex-G⁺ = {!!}

     Lex-G-∉̂ᴱ : ∀ {n} {i : Fin n} x y p q (i∉p : toℕ i ∉̂ᴱ p) (i∉q : toℕ i ∉̂ᴱ q) → toℕ i ∉̂ᴱ (G x y p q)
     Lex-G-∉̂ᴱ = {!!}

     Lex-G-dist : ∀ {n} {i j : Fin n} x y p q →  (toℕ i , toℕ j) ∷ (G x y p p) ≡ (G x y ((toℕ i , toℕ j) ∷ p) ((toℕ i , toℕ j) ∷ q)) 
     Lex-G-dist = {!!} 

     cnc : f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ ((f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))))
     cnc =  {!!}

{- Here is what I want to do, but need to do this reasoning with ≈⁺ ... 

              f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s)))                           < cong and Lex-G⁺ > 
              f ▷⁺ (valid (x ⊕ y , G(x, y, r, s))                                 < Lex-G-∉̂ᴱ and ▷⁺-valid > 
              (valid (f ▷ (x ⊕ y) , (i, j) :: G(x, y, r, s))                      < cong and dst>
              (valid ((f ▷ x) ⊕ (f ▷ y) , (i, j) :: G(x, y, r, s))                < cong and Lex-G-dist > 
              (valid ((f ▷ x) ⊕ (f ▷ y) ,  G(x, y, (i, j) :: r, (i, j) :: s))     < sym and Lex-G⁺ > 
              valid (f ▷ x , (i, j) ::r) ⊕⁺ valid (f ▷ y , (i, j) :: s)           < ▷⁺-valid twice, with cong > 
              ((f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))))
-}
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {invalid}       {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _     = cnc
    where
--  cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (invalid ⊕⁺ invalid) , (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ invalid) ]
    cnc : IsLevel k PathDistributiveIn[ invalid , invalid ]
    cnc = {!!}
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r _ = cnc 
    where
    cnc : IsLevel k PathDistributiveIn[ f ▷⁺ ((valid (x , r)) ⊕⁺ invalid) , (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ invalid) ]    
    cnc = {!!} 
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {invalid} {valid (y , s)}        ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ i∉s = cnc 
    where
    cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (invalid ⊕⁺ (valid (y , s)) ) , (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ (valid (y , s))) ]    
    cnc = {!!} 
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {valid (y , s)}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s = cnc 
    where

    dst : Level_DistributiveIn[_,_] A k (f ▷ (x ⊕ y)) ((f ▷ x) ⊕ (f ▷ y)) 
    dst = dist f (eqr ⊥≤x) (eqr x≤⊤)  (eqr ⊥≤y) (eqr y≤⊤)

    cnc : IsLevel k PathDistributiveIn[ f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s)) ) , (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))) ]    
    cnc = {!  !} 
    -- Hmmmm .... 
