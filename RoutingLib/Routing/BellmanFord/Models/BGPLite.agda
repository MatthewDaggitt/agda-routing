open import Data.Nat using (ℕ)
open import Data.Nat.Properties
  using (_<?_; <-cmp; <-trans; <-irrefl; <-asym; m+n≮n; m≤m+n; <⇒≱; ≤-refl; ≤-trans)
open import Data.List using (List)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; fromℕ≤)
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

open import RoutingLib.Data.Path.Certified.FiniteEdge
  using (Path; invalid; valid; []; _∷_∣_∣_; _∷_; _≈ₚ_)
open import RoutingLib.Data.Path.Certified.FiniteEdge.Properties
  using (≈ₚ-refl)
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty using (_∈_; _⇿_)
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Properties
  using (⇿-resp-≈ₚ; ∉-resp-≈ₚ; ≈ₚ-sym; ≈ₚ-trans)
open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty
  using (Pathⁿᵗ; []; _∷_; length)
open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty.Properties
  using (_⇿?_)
  renaming (_∈?_ to _∈ₚ?_)
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Certify
open import RoutingLib.Asynchronous
import RoutingLib.Routing.BellmanFord.Theorems as ConvergenceTheorems
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.BellmanFord.Models.BGPLite (n : ℕ) where

open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route n
open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route.Properties n
open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Policy n
open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Communities

open import Algebra.FunctionProperties _≈ᵣ_
open module Choice = NaturalChoice ≤ᵣ-totalOrder

------------
-- Syntax --
------------

data Step : Set₁ where
  step : Node → Node → Policy → Step

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
_▷_ : Step → Route → Route
_              ▷ invalid       = invalid
(step i j pol) ▷ (valid x c p) with (i , j) ⇿? p | i ∈ₚ? p
... | no  _    | _       = invalid
... | yes _    | yes _   = invalid
... | yes ij⇿p | no  i∈p = apply pol (valid x c ((i , j) ∷ p))

▷-cong : ∀ f {r s} → r ≈ᵣ s → f ▷ r ≈ᵣ f ▷ s
▷-cong (step i j pol) {_}              {_}              invalidEq = invalidEq
▷-cong (step i j pol) {(valid l cs p)} {(valid k ds q)} (validEq l≡k cs≈ds refl)
  with (i , j) ⇿? p | i ∈ₚ? p
... | no  _ | _     = invalidEq
... | yes _ | yes _ = invalidEq
... | yes _ | no  _ = apply-cong pol (validEq l≡k cs≈ds refl)

---------------------
-- Choice operator --
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

open RightNaturalOrder _≈ᵣ_ _⊕_ using () renaming (_≤_ to _≤₊_)

-----------
-- Steps --
-----------

▷-zero : ∀ f → f ▷ invalid ≈ᵣ invalid
▷-zero (step _ _ _) = invalidEq

▷-increasing : ∀ f x → x ≤₊ f ▷ x
▷-increasing f              invalid        = ≈ᵣ-refl
▷-increasing (step i j pol) (valid l cs p) with (i , j) ⇿? p | i ∈ₚ? p
... | no  _   | _       = ≈ᵣ-refl
... | yes _   | yes _   = ≈ᵣ-refl
... | yes i⇿p | no  i∉p with ≤ᵣ-total (apply pol (valid l cs ((i , j) ∷ p))) (valid l cs p)
...   | inj₂ r≤e▷r = ≈ᵣ-refl
...   | inj₁ e▷r≤r = contradiction e▷r≤r (apply-nonDecreasing pol)

--------------------------------
-- A specific routing problem --
--------------------------------

module _ (topology : Fin n → Fin n → Policy) where

  A : Fin n → Fin n → Step
  A i j = step i j (topology i j)

  ------------------------------
  -- Path projection function --
  ------------------------------

  path : Route → Path n
  path invalid       = invalid
  path (valid _ _ p) = valid (certify p)

  path-cong : ∀ {r s} → r ≈ᵣ s → path r ≈ₚ path s
  path-cong invalidEq          = invalid
  path-cong (validEq _ _ refl) = ≈ₚ-refl

  r≈0⇒path[r]≈[] : ∀ {r} → r ≈ᵣ 0# → path r ≈ₚ valid []
  r≈0⇒path[r]≈[] (validEq _ _ refl) = ≈ₚ-refl
  
  r≈∞⇒path[r]≈∅ : ∀ {r} → r ≈ᵣ invalid → path r ≈ₚ invalid
  r≈∞⇒path[r]≈∅ invalidEq = invalid

  path[r]≈∅⇒r≈∞ : ∀ {r} → path r ≈ₚ invalid → r ≈ᵣ invalid
  path[r]≈∅⇒r≈∞ {invalid}      invalid = invalidEq
  path[r]≈∅⇒r≈∞ {valid l cs p} ()

  path-reject : ∀ {i j r q} → path r ≈ₚ valid q → ¬ (i , j) ⇿ q ⊎ i ∈ q → A i j ▷ r ≈ᵣ invalid
  path-reject {i} {j} {invalid}      pᵣ≈p        inv = invalidEq
  path-reject {i} {j} {valid l cs p} (valid p≈q) inv with (i , j) ⇿? p | i ∈ₚ? p
  ... | no  _    | _       = invalidEq
  ... | yes _    | yes _   = invalidEq
  ... | yes ij⇿p | no  i∉p with inv
  ...   | inj₁ ¬ij⇿p = contradiction (⇿-resp-≈ₚ p≈q (⇿-certify ij⇿p)) ¬ij⇿p
  ...   | inj₂ i∈p   = contradiction (∉-resp-≈ₚ p≈q (∉-certify i∉p)) i∈p

  path-accept : ∀ {i j r q} → path r ≈ₚ valid q → A i j ▷ r ≉ᵣ invalid →
                ∀ ij⇿q i∉q → path (A i j ▷ r) ≈ₚ valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q)
  path-accept {i} {j} {invalid}      pᵣ≈q        Aᵢⱼ▷r≉0 e⇿q i∉q = contradiction invalidEq Aᵢⱼ▷r≉0
  path-accept {i} {j} {valid l cs p} (valid p≈q) Aᵢⱼ▷r≉0 _   _ with (i , j) ⇿? p | i ∈ₚ? p
  ... | no ¬e⇿p | _       = contradiction invalidEq Aᵢⱼ▷r≉0
  ... | yes _   | yes i∈p = contradiction invalidEq Aᵢⱼ▷r≉0
  ... | yes e⇿p | no  i∉p
    with apply (topology i j) (valid l cs ((i , j) ∷ p))
         | inspect (apply (topology i j)) (valid l cs ((i , j) ∷ p))
  ... | invalid     | _      = contradiction invalidEq Aᵢⱼ▷r≉0
  ... | valid _ _ _ | [ eq ] with apply-increasing (topology i j) eq
  ...   | _ , refl = valid (≈ₚ-trans (certify-accept e⇿p i∉p) (refl ∷ p≈q))

  --------------
  -- Algebras --
  --------------

  rawRoutingAlgebra : RawRoutingAlgebra _ _ _
  rawRoutingAlgebra = record
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

  rawPathAlgebra : RawPathAlgebra _ _ _ _
  rawPathAlgebra = record
    { rawRoutingAlgebra = rawRoutingAlgebra
    ; A                 = A
    ; path              = path
    }

  isRoutingAlgebra : IsRoutingAlgebra rawRoutingAlgebra
  isRoutingAlgebra = record
    { ⊕-sel              = ⊕-sel
    ; ⊕-comm             = ⊕-comm
    ; ⊕-assoc            = ⊕-assoc
    ; ⊕-zeroʳ            = ⊕-zeroʳ
    ; ⊕-identityʳ        = ⊕-identityʳ
    ; ▷-zero             = ▷-zero
    }

  isPathAlgebra : IsPathAlgebra rawPathAlgebra
  isPathAlgebra = record
    { isRoutingAlgebra = isRoutingAlgebra
    ; path-cong        = path-cong
    ; r≈0⇒path[r]≈[]   = r≈0⇒path[r]≈[]
    ; r≈∞⇒path[r]≈∅    = r≈∞⇒path[r]≈∅
    ; path[r]≈∅⇒r≈∞    = path[r]≈∅⇒r≈∞
    ; path-reject      = path-reject
    ; path-accept      = path-accept
    }

  isIncreasingPathAlgebra : IsIncreasingPathAlgebra rawPathAlgebra
  isIncreasingPathAlgebra = record
    { isPathAlgebra = isPathAlgebra
    ; ▷-increasing  = ▷-increasing
    }

  increasingPathAlgebra : IncreasingPathAlgebra _ _ _ _
  increasingPathAlgebra = record
    { isIncreasingPathAlgebra = isIncreasingPathAlgebra
    }

  -----------------
  -- Convergence --
  -----------------

  open BellmanFord rawRoutingAlgebra A

  δ-convergesAbsolutely : IsAsynchronouslySafe σ∥
  δ-convergesAbsolutely = ConvergenceTheorems.incrPaths-converges increasingPathAlgebra
