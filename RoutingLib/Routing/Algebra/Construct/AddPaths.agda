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
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.EqReasoning S
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using ()
open import RoutingLib.Algebra.Construct.Lexicographic as Lex using (Lex)
open import RoutingLib.Function
open import RoutingLib.Relation.Nullary.Construct.Add.Point
  renaming (∙ to invalid; [_] to valid)
open import RoutingLib.Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq) using (∙≈∙; [_])
open import RoutingLib.Data.Path.Uncertified
open import RoutingLib.Data.Path.Uncertified.Choice
open import RoutingLib.Data.Path.Uncertified.Properties



infix 4 _≈⁺_ _≉⁺_
infix 7 _⊕⁺_
infix 6 _▷⁺_

Route⁺ : Set a
Route⁺ = Pointed (Route × Path)

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
  ≈ₓ-refl : Reflexive (Pointwise {A₂ = Path} _≈_ _≡_)
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
  (Lex.sel {_≈₂_ = _≡_} _≟_ _⊕_ _⊓ₗₑₓ_ ≈-refl (refl {A = Path}) ⊕-sel ⊓ₗₑₓ-sel)

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

▷⁺-reject : ∀ {n} {i j : Fin n} (f : Step i j) x p →
            f ▷ x ≈ ∞# → f ▷⁺ (valid (x , p)) ≈⁺ ∞#⁺
▷⁺-reject {_} {i} {j} f x p f▷x≈∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  _ | _     | _         = ∙≈∙
... | yes _ | yes _ | _         = ∙≈∙
... | yes _ | no  _ | yes _     = ∙≈∙
... | yes _ | no  _ | no  f▷x≉∞ = contradiction f▷x≈∞ f▷x≉∞

▷⁺-accept : ∀ {n} {i j : Fin n} (f : Step i j) x p →
            (toℕ i , toℕ j) ⇿ p → toℕ i ∉ₚ p → f ▷ x ≉ ∞# →
            f ▷⁺ (valid (x , p)) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ p)
▷⁺-accept {_} {i} {j} f x p ij⇿p i∉p f▷x≉∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no ¬ij⇿p | _       | _         = contradiction ij⇿p ¬ij⇿p
... | yes _    | yes i∈p | _         = contradiction i∈p i∉p
... | yes _    | no  _   | yes f▷x≈∞ = contradiction f▷x≈∞ f▷x≉∞
... | yes _    | no  _   | no  _     = [ ≈-refl , refl ]

--------------------------------------------------------------------------------
-- The resulting algebra is a path algebra

path : Route⁺ → Maybe Path
path invalid         = invalid
path (valid (x , p)) = valid p

path-cong : path Preserves _≈⁺_ ⟶ _≡_
path-cong ∙≈∙          = refl
path-cong [ _ , refl ] = refl

r≈0⇒path[r]≈[] : ∀ {r} → r ≈⁺ 0#⁺ → path r ≡ valid []
r≈0⇒path[r]≈[] [ _ , refl ] = refl
r≈∞⇒path[r]≈∅ : ∀ {r} → r ≈⁺ ∞#⁺ → path r ≡ invalid
r≈∞⇒path[r]≈∅ ∙≈∙ = refl

path[r]≈∅⇒r≈∞ : ∀ {r} → path r ≡ invalid → r ≈⁺ ∞#⁺
path[r]≈∅⇒r≈∞ {invalid} refl = ∙≈∙
path[r]≈∅⇒r≈∞ {valid x} ()

path-reject : ∀ {n} {i j : Fin n} {r p} (f : Step⁺ i j) →
              path r ≡ valid p → ¬ (toℕ i , toℕ j) ⇿ p ⊎ toℕ i ∈ₚ p →
              f ▷⁺ r ≈⁺ ∞#⁺
path-reject {i = i} {j} {invalid}       f _    v = ∙≈∙
path-reject {i = i} {j} {valid (x , p)} f refl v
  with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  _    | _       | _           = ∙≈∙
... | yes _    | yes _   | _           = ∙≈∙
... | yes _    | no  _   | yes _       = ∙≈∙
... | yes ij⇿p | no  i∉p | no  f∞▷x≉∞ = Sum.[ contradiction ij⇿p , contradiction ◌ i∉p ] v

path-accept : ∀ {n} {i j : Fin n} {r p} (f : Step⁺ i j) →
              path r ≡ valid p → f ▷⁺ r ≉⁺ ∞#⁺ →
              path (f ▷⁺ r) ≡ valid ((toℕ i , toℕ j) ∷ p)
path-accept {i = i} {j} {invalid}       f _    f▷r≉∞ = contradiction ∙≈∙ f▷r≉∞
path-accept {i = i} {j} {valid (x , p)} f refl f▷r≉∞
  with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
... | no  _    | _       | _           = contradiction ∙≈∙ f▷r≉∞
... | yes _    | yes _   | _           = contradiction ∙≈∙ f▷r≉∞
... | yes _    | no  _   | yes _       = contradiction ∙≈∙ f▷r≉∞
... | yes ij⇿p | no  i∉p | no  f∞▷x≉∞ = refl

isPathAlgebra : IsPathAlgebra AddPaths
isPathAlgebra = record
  { path           = path
  ; path-cong      = path-cong
  ; r≈0⇒path[r]≈[] = r≈0⇒path[r]≈[]
  ; r≈∞⇒path[r]≈∅  = r≈∞⇒path[r]≈∅
  ; path[r]≈∅⇒r≈∞  = path[r]≈∅⇒r≈∞
  ; path-reject    = path-reject
  ; path-accept    = path-accept
  }


--------------------------------------------------------------------------------
-- Properties preserved

open PathDistributivity isPathAlgebra

module _ (⊕-sel : Selective _≈_ _⊕_) (⊕-identityˡ : LeftIdentity _≈_ ∞# _⊕_) where
  
  open IsDecEquivalence ≈⁺-isDecEquivalence
    using () renaming (trans to ≈⁺-trans)

  ⊕ˡ-sel : Selective (Pointwise _≈_ _≡_) (Lex _≟_ _⊕_ _⊓ₗₑₓ_)
  ⊕ˡ-sel = {!!}

  lemma1 : ∀ {⊤ ⊥} → Level_DistributiveIn[_,_] A 0 ⊥ ⊤ → 
           ∀ {n} {i j : Fin n} {f : Step i j} {x y p q} →
           ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
           f ▷ x ≈ ∞# → valid (x , p) ⊕⁺ valid (y , q) ≈⁺ valid (x , p) → f ▷ y ≈ ∞#
  lemma1 distrib {f = f} {x} {y} {p} {q} ⊥≤x x≤⊤ ⊥≤y y≤⊤ f▷x≈∞ xp⊕yq≈xp = begin
    f ▷ y             ≈⟨ ≈-sym (⊕-identityˡ (f ▷ y)) ⟩
    ∞# ⊕ (f ▷ y)       ≈⟨ ⊕-cong (≈-sym f▷x≈∞) ≈-refl ⟩
    (f ▷ x) ⊕ (f ▷ y) ≈⟨ ≈-sym (distrib f ⊥≤x x≤⊤ ⊥≤y y≤⊤) ⟩
    f ▷ (x ⊕ y)       ≈⟨ ▷-cong f {!!} ⟩
    f ▷ x             ≈⟨ f▷x≈∞ ⟩
    ∞#                 ∎
  
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
  pres-distrib {zero} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {valid (y , s)} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s (just ij⇿r) (just ij⇿s)
    with toℕ i ∈ₚ? r | toℕ i ∈ₚ? s | (toℕ i , toℕ j) ⇿? r | (toℕ i , toℕ j) ⇿? s
  ... | yes i∈r | _       | _        | _        = contradiction (valid i∈r) i∉r
  ... | _       | yes i∈s | _        | _        = contradiction (valid i∈s) i∉s
  ... | _       | _       | no ¬ij⇿r | _        = contradiction ij⇿r ¬ij⇿r
  ... | _       | _       | _        | no ¬ij⇿s = contradiction ij⇿s ¬ij⇿s
  ... | no _    | no _    | yes _    | yes _ with f ▷ x ≟ ∞# | f ▷ y ≟ ∞#
  ...   | yes f▷x≈∞  | yes f▷y≈∞  = test2
     where
     test2 : f ▷⁺ (valid (x , r) ⊕⁺ valid (y , s)) ≈⁺ ∞#⁺
     test2 with ⊕⁺-sel ⊕-sel (valid (x , r)) (valid (y , s))
     ... | inj₁ eq = ≈⁺-trans (▷⁺-cong f eq) (▷⁺-reject f x r f▷x≈∞)
     ... | inj₂ eq = ≈⁺-trans (▷⁺-cong f eq) (▷⁺-reject f y s f▷y≈∞)
  ...   | yes f▷x≈∞  | no  f▷y≉∞  = test2
     where
     test2 :  f ▷⁺ (valid (x , r) ⊕⁺ valid (y , s)) ≈⁺ (valid (f ▷ y , (toℕ i , toℕ j) ∷ s))
     test2 with ⊕⁺-sel ⊕-sel (valid (x , r)) (valid (y , s))
     ... | inj₂ eq = ≈⁺-trans (▷⁺-cong f eq) (▷⁺-accept f y s ij⇿s (i∉s ∘ just) f▷y≉∞)
     ... | inj₁ eq = contradiction {!!} f▷y≉∞
  ...   | no  f▷x≉∞  | yes f▷y≈∞  = {!!}
  ...   | no  f▷x≉∞  | no  f▷y≉∞  = {!!}
  pres-distrib {suc k} {⊤} {⊥} dist p q =  {!!}


{-
    with ⊕ˡ-sel (x , r) (y , s)
  ... | inj₁ xr⊕ys≈xr = {!!}
    where
    lemma : f ▷⁺ (x , r) ≈ f 
  ... | inj₂ xr⊕ys≈ys = {!!}
-}
