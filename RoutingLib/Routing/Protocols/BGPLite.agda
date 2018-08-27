open import Data.Nat using (ℕ)
open import Data.Nat.Properties
  using (_<?_; <-cmp; <-trans; <-irrefl; <-asym; m+n≮n; m≤m+n; <⇒≱; ≤-refl; ≤-trans)
open import Data.List using (List)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong; cong₂; inspect; [_])
open import Relation.Binary using (Minimum; Maximum)
open import Level using () renaming (zero to ℓ₀; suc to lsuc)

import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder
import RoutingLib.Algebra.Selectivity.NaturalChoice.Min.TotalOrder as NaturalChoice

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.PathAlgebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra

open import RoutingLib.Data.Path.UncertifiedI
open import RoutingLib.Data.Path.UncertifiedI.Properties

open import RoutingLib.Routing.Protocols.BGPLite.Route
open import RoutingLib.Routing.Protocols.BGPLite.Route.Properties
open import RoutingLib.Routing.Protocols.BGPLite.Policy
open import RoutingLib.Routing.Protocols.BGPLite.Communities

module RoutingLib.Routing.Protocols.BGPLite where

open import Algebra.FunctionProperties _≈ᵣ_
open module Choice = NaturalChoice ≤ᵣ-totalOrder

-----------------
-- Raw algebra --
-----------------

data Step {n} (i j : Fin n) : Set₁ where
  step : Policy → Step i j

0# : Route
0# = valid 0 ∅ []

∞ : Route
∞ = invalid

infix 5 _⊕_
_⊕_ : Op₂ Route
_⊕_ = Choice._⊓_

⊕-cong : Congruent₂ _⊕_
⊕-cong = Choice.⊓-cong

infix 5 _▷_
_▷_ : ∀ {n} {i j : Fin n} → Step i j → Route → Route
_▷_ {_} {_} {_} _          invalid       = invalid
_▷_ {_} {i} {j} (step pol) (valid x c p) with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _    | _       = invalid
... | yes _    | yes _   = invalid
... | yes ij⇿p | no  i∈p = apply pol (valid x c ((toℕ i , toℕ j) ∷ p))

▷-cong : ∀ {n} {i j : Fin n} (f : Step i j) {r s} → r ≈ᵣ s → f ▷ r ≈ᵣ f ▷ s
▷-cong {_} {_} {_} (step pol) {_}              {_}              invalidEq = invalidEq
▷-cong {_} {i} {j} (step pol) {(valid l cs p)} {(valid k ds q)} (validEq l≡k cs≈ds refl)
  with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _ | _     = invalidEq
... | yes _ | yes _ = invalidEq
... | yes _ | no  _ = apply-cong pol (validEq l≡k cs≈ds refl)

algebra : RawRoutingAlgebra _ _ _
algebra = record
  { Step               = Step
  ; Route              = Route
  ; _≈_                = _≈ᵣ_
  ; _⊕_                = _⊕_
  ; _▷_                = _▷_
  ; 0#                 = 0#
  ; ∞                  = ∞
  ; ≈-isDecEquivalence = ≈ᵣ-isDecEquivalence
  ; ▷-cong             = ▷-cong
  ; ⊕-cong             = ⊕-cong
  }

---------------------
-- Routing algebra --
---------------------

⊕-sel : Selective _⊕_
⊕-sel = Choice.⊓-sel

⊕-assoc : Associative _⊕_
⊕-assoc = Choice.⊓-assoc

⊕-comm : Commutative _⊕_
⊕-comm = Choice.⊓-comm

⊕-identityʳ  : RightIdentity invalid _⊕_
⊕-identityʳ = Choice.⊓-identityʳ ≤ᵣ-maximum

⊕-zeroʳ : RightZero 0# _⊕_
⊕-zeroʳ = Choice.⊓-zeroʳ ≤ᵣ-minimum

▷-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷ invalid ≈ᵣ invalid
▷-fixedPoint (step _) = invalidEq

isRoutingAlgebra : IsRoutingAlgebra algebra
isRoutingAlgebra = record
  { ⊕-sel        = ⊕-sel
  ; ⊕-comm       = ⊕-comm
  ; ⊕-assoc      = ⊕-assoc
  ; ⊕-zeroʳ      = ⊕-zeroʳ
  ; ⊕-identityʳ  = ⊕-identityʳ
  ; ▷-fixedPoint = ▷-fixedPoint
  }

------------------
-- Path algebra --
------------------

path : Route → Path
path invalid       = invalid
path (valid _ _ p) = valid p

path-cong : ∀ {r s} → r ≈ᵣ s → path r ≡ path s
path-cong invalidEq          = refl
path-cong (validEq _ _ refl) = refl

r≈0⇒path[r]≈[] : ∀ {r} → r ≈ᵣ 0# → path r ≡ valid []
r≈0⇒path[r]≈[] (validEq _ _ refl) = refl

r≈∞⇒path[r]≈∅ : ∀ {r} → r ≈ᵣ invalid → path r ≡ invalid
r≈∞⇒path[r]≈∅ invalidEq = refl

path[r]≈∅⇒r≈∞ : ∀ {r} → path r ≡ invalid → r ≈ᵣ invalid
path[r]≈∅⇒r≈∞ {invalid}      refl = invalidEq
path[r]≈∅⇒r≈∞ {valid l cs p} ()

path-reject : ∀ {n} {i j : Fin n} {r q} (f : Step i j) → path r ≡ valid q →
              ¬ (toℕ i , toℕ j) ⇿ᵥ q ⊎ toℕ i ∈ᵥₚ q → f ▷ r ≈ᵣ invalid
path-reject {_} {i} {j} {invalid}      (step pol) pᵣ≈p inv = invalidEq
path-reject {_} {i} {j} {valid l cs p} (step pol) refl inv with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _    | _       = invalidEq
... | yes _    | yes _   = invalidEq
... | yes ij⇿p | no  i∉p with inv
...   | inj₁ ¬ij⇿p = contradiction ij⇿p ¬ij⇿p
...   | inj₂ i∈p   = contradiction i∈p i∉p

path-accept : ∀ {n} {i j : Fin n} {r q} (f : Step i j) → path r ≡ valid q → f ▷ r ≉ᵣ invalid →
              path (f ▷ r) ≡ valid ((toℕ i , toℕ j) ∷ q)
path-accept {_} {i} {j} {invalid}      (step pol) pᵣ≈q f▷r≉0 = contradiction invalidEq f▷r≉0
path-accept {_} {i} {j} {valid l cs p} (step pol) refl f▷r≉0 with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no ¬e⇿p | _       = contradiction invalidEq f▷r≉0
... | yes _   | yes i∈p = contradiction invalidEq f▷r≉0
... | yes e⇿p | no  i∉p
  with apply pol (valid l cs ((toℕ i , toℕ j) ∷ p))
       | inspect (apply pol) (valid l cs ((toℕ i , toℕ j) ∷ p))
... | invalid     | _      = contradiction invalidEq f▷r≉0
... | valid _ _ _ | [ eq ] with apply-increasing pol eq
...   | _ , refl = refl

isPathAlgebra : IsPathAlgebra algebra
isPathAlgebra = record
  { isRoutingAlgebra = isRoutingAlgebra
  ; path-cong        = path-cong
  ; r≈0⇒path[r]≈[]   = r≈0⇒path[r]≈[]
  ; r≈∞⇒path[r]≈∅    = r≈∞⇒path[r]≈∅
  ; path[r]≈∅⇒r≈∞    = path[r]≈∅⇒r≈∞
  ; path-reject      = path-reject
  ; path-accept      = path-accept
  }

----------------------
-- Other properties --
----------------------

open RightNaturalOrder _≈ᵣ_ _⊕_ using () renaming (_≤_ to _≤₊_)

isIncreasing : IsIncreasing algebra
isIncreasing {_} {_} {_} f          invalid        = ≈ᵣ-refl
isIncreasing {_} {i} {j} (step pol) (valid l cs p) with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _   | _       = ≈ᵣ-refl
... | yes _   | yes _   = ≈ᵣ-refl
... | yes i⇿p | no  i∉p with ≤ᵣ-total (apply pol (valid l cs ((toℕ i , toℕ j) ∷ p))) (valid l cs p)
...   | inj₂ r≤e▷r = ≈ᵣ-refl
...   | inj₁ e▷r≤r = contradiction e▷r≤r (apply-nonDecreasing pol)
