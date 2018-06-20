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

open import RoutingLib.Data.Nat.Properties using (n≢1+n)
open import RoutingLib.Data.SimplePath
  using (SimplePath; invalid; valid)
open import RoutingLib.Data.SimplePath.Relation.Equality hiding (≈ₚ-sym; p≉i∷p)
open import RoutingLib.Data.SimplePath.NonEmpty
  using (SimplePathⁿᵗ; []; _∷_∣_∣_; length; _⇿_; _∉_; _∈_)
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality using (≈ₚ-sym; p≉i∷p)
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Lex
  using (_<ₗₑₓ_; <ₗₑₓ-cmp; <ₗₑₓ-trans; <ₗₑₓ-resp-≈ₚ; <ₗₑₓ-asym; <ₗₑₓ-irrefl; <ₗₑₓ-minimum; <ₗₑₓ-respˡ-≈ₚ; <ₗₑₓ-respʳ-≈ₚ)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties
  using (_⇿?_; ⇿-resp-≈ₚ; ∉-resp-≈ₚ; length-cong)
  renaming (_∈?_ to _∈ₚ?_; _∉?_ to _∉ₚ?_)
import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder
open import RoutingLib.Routing.Algebra
import RoutingLib.Algebra.Selectivity.NaturalChoice.Min.TotalOrder as NaturalChoice

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
(step i j pol) ▷ (valid x c p) with (i , j) ⇿? p | i ∉ₚ? p
... | no  _   | _       = invalid
... | yes _   | no  _   = invalid
... | yes i⇿p | yes i∉p = apply pol (valid x c ((i , j) ∷ p ∣ i⇿p ∣ i∉p))

▷-cong : ∀ f {r s} → r ≈ᵣ s → f ▷ r ≈ᵣ f ▷ s
▷-cong (step i j pol) {_}                {_}                invalidEq = invalidEq
▷-cong (step i j pol) {r@(valid l cs p)} {s@(valid k ds q)} r≈s@(validEq l≡k cs≈ds p≈q)
  with (i , j) ⇿? p | (i , j) ⇿? q
... | no _    | no _    = invalidEq 
... | no ¬e⇿p | yes e⇿q = contradiction (⇿-resp-≈ₚ (≈ₚ-sym p≈q) e⇿q) ¬e⇿p
... | yes e⇿p | no ¬e⇿q = contradiction (⇿-resp-≈ₚ p≈q e⇿p) ¬e⇿q
... | yes _   | yes _ with i ∉ₚ? p | i ∉ₚ? q
...   | no _    | no  _   = invalidEq 
...   | no  i∈p | yes i∉q = contradiction (∉-resp-≈ₚ (≈ₚ-sym p≈q) i∉q) i∈p
...   | yes i∉p | no  i∈q = contradiction (∉-resp-≈ₚ p≈q i∉p) i∈q
...   | yes _  | yes _  with
  apply pol r | apply pol s | inspect (apply pol) r | inspect (apply pol) s
...     | invalid     | invalid     | _        | _ = invalidEq
...     | invalid     | valid _ _ _ | [ pᵣ≡i ] | [ pₛ≡r ] =
  contradiction (apply-trans pol r≈s pᵣ≡i pₛ≡r) λ()
...     | valid _ _ _ | invalid     | [ pᵣ≡r ] | [ pₛ≡i ] =
  contradiction (apply-trans pol r≈s pᵣ≡r pₛ≡i) λ()
...     | valid _ _ _ | valid _ _ _ | [ pᵣ≡r ] | [ pₛ≡r ] with apply-trans pol r≈s pᵣ≡r pₛ≡r
...       | validEq leq ceq _ = validEq leq ceq (refl ∷ p≈q)


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
▷-increasing (step i j pol) (valid l cs p) with (i , j) ⇿? p | i ∉ₚ? p
... | no  _   | _       = ≈ᵣ-refl
... | yes _   | no  _   = ≈ᵣ-refl
... | yes i⇿p | yes i∉p with apply pol (valid l cs p) | inspect (apply pol) (valid l cs p)
...   | invalid      | _         = ≈ᵣ-refl
...   | valid k ds _ | [ app≡s ] with ≤ᵣ-total (valid k ds ((i , j) ∷ p ∣ i⇿p ∣ i∉p)) (valid l cs p)
...     | inj₂ _                       = ≈ᵣ-refl
...     | inj₁ (level<  k<l)           = contradiction (apply-levelIncr pol (≈ᵣ-reflexive app≡s)) (<⇒≱ k<l)
...     | inj₁ (length< _ |i∷p|<|p|)   = contradiction |i∷p|<|p| (m+n≮n 1 _)
...     | inj₁ (plex<   _ |i∷p|≡|p| _) = contradiction (sym |i∷p|≡|p|) (n≢1+n _)
...     | inj₁ (comm≤   _ i∷p≈p     _) = contradiction (≈ₚ-sym i∷p≈p) p≉i∷p

--------------------------------
-- A specific routing problem --
--------------------------------

postulate topology : Fin n → Fin n → Policy

A : Fin n → Fin n → Step
A i j = step i j (topology i j)

------------------------------
-- Path projection function --
------------------------------

path : Route → SimplePath n
path invalid       = invalid
path (valid _ _ p) = valid p

path-cong : ∀ {r s} → r ≈ᵣ s → path r ≈ₚ path s
path-cong invalidEq         = invalid
path-cong (validEq _ _ p≈q) = valid p≈q

r≈0⇒path[r]≈[] : ∀ {r} → r ≈ᵣ 0# → path r ≈ₚ valid []
r≈0⇒path[r]≈[] (validEq _ _ []) = valid []

r≈∞⇒path[r]≈∅ : ∀ {r} → r ≈ᵣ invalid → path r ≈ₚ invalid
r≈∞⇒path[r]≈∅ invalidEq = invalid

path[r]≈∅⇒r≈∞ : ∀ {r} → path r ≈ₚ invalid → r ≈ᵣ invalid
path[r]≈∅⇒r≈∞ {invalid}      invalid = invalidEq
path[r]≈∅⇒r≈∞ {valid l cs p} ()

path-reject : ∀ {i j r q} → path r ≈ₚ valid q → ¬ (i , j) ⇿ q ⊎ i ∈ q → A i j ▷ r ≈ᵣ invalid
path-reject {i} {j} {invalid}      pᵣ≈p        inv = invalidEq
path-reject {i} {j} {valid l cs p} (valid p≈q) inv with (i , j) ⇿? p | i ∉ₚ? p
... | no  _    | _       = invalidEq
... | yes _    | no  _   = invalidEq
... | yes ij⇿p | yes i∉p with inv
...   | inj₁ ¬ij⇿p = contradiction (⇿-resp-≈ₚ p≈q ij⇿p) ¬ij⇿p
...   | inj₂ i∈p   = contradiction (∉-resp-≈ₚ p≈q i∉p) i∈p

path-accept : ∀ {i j r q} → path r ≈ₚ valid q → A i j ▷ r ≉ᵣ invalid →
              ∀ ij⇿q i∉q → path (A i j ▷ r) ≈ₚ valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q)
path-accept {i} {j} {invalid}      pᵣ≈q        Aᵢⱼ▷r≉0 ij⇿q i∉q = contradiction invalidEq Aᵢⱼ▷r≉0
path-accept {i} {j} {valid l cs p} (valid p≈q) Aᵢⱼ▷r≉0 ij⇿q i∉q with (i , j) ⇿? p | i ∉ₚ? p
... | no ¬ij⇿p | _       = contradiction (⇿-resp-≈ₚ (≈ₚ-sym p≈q) ij⇿q) ¬ij⇿p
... | yes _    | no  i∈p = contradiction (∉-resp-≈ₚ (≈ₚ-sym p≈q) i∉q) i∈p
... | yes _    | yes _   with apply (topology i j) (valid l cs p)
...   | invalid     = contradiction invalidEq Aᵢⱼ▷r≉0
...   | valid _ _ _ = valid (refl ∷ p≈q)

--------------
-- Algebras --
--------------

isRoutingAlgebra : IsRoutingAlgebra _≈ᵣ_ _⊕_ _▷_ 0# ∞
isRoutingAlgebra = record
  { ≈-isDecEquivalence = ≈ᵣ-isDecEquivalence
  ; ⊕-cong             = ⊕-cong
  ; ⊕-sel              = ⊕-sel
  ; ⊕-comm             = ⊕-comm
  ; ⊕-assoc            = ⊕-assoc
  ; ⊕-zeroʳ            = ⊕-zeroʳ
  ; ⊕-identityʳ        = ⊕-identityʳ
  ; ▷-cong             = ▷-cong
  ; ▷-zero             = ▷-zero
  }

isPathAlgebra : IsPathAlgebra _≈ᵣ_ _⊕_ _▷_ 0# ∞ A path
isPathAlgebra = record
  { isRoutingAlgebra = isRoutingAlgebra
  ; path-cong        = path-cong
  ; r≈0⇒path[r]≈[]   = r≈0⇒path[r]≈[]
  ; r≈∞⇒path[r]≈∅    = r≈∞⇒path[r]≈∅
  ; path[r]≈∅⇒r≈∞    = path[r]≈∅⇒r≈∞
  ; path-reject      = path-reject
  ; path-accept      = path-accept
  }

isIncreasingPathAlgebra : IsIncreasingPathAlgebra _≈ᵣ_ _⊕_ _▷_ 0# ∞ A path
isIncreasingPathAlgebra = record
  { isPathAlgebra = isPathAlgebra
  ; ▷-increasing  = ▷-increasing
  }

increasingPathAlgebra : IncreasingPathAlgebra _ _ _ _
increasingPathAlgebra = record
  { isIncreasingPathAlgebra = isIncreasingPathAlgebra
  }

routingAlgebra : RoutingAlgebra _ _ _
routingAlgebra = record
  { isRoutingAlgebra = isRoutingAlgebra
  }
