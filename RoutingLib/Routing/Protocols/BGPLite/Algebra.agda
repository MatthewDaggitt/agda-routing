open import Algebra.FunctionProperties
open import Data.Nat using (ℕ; _≟_)
open import Data.Nat.Properties
  using (_<?_; <-trans; <-irrefl; <-asym; m+n≮n; m≤m+n; <⇒≱; ≤-refl; ≤-trans)
  renaming (<-cmp to compare)
open import Data.List using (List)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; inspect; [_]; module ≡-Reasoning)
open import Relation.Binary using (Minimum; Maximum)
open import Level using () renaming (zero to ℓ₀; suc to lsuc)

import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder as NaturalChoice

open import RoutingLib.Data.Path.Uncertified using (inflate; deflate; length)
open import RoutingLib.Data.Path.Uncertified.Properties
  using (∈-deflate⁻; deflate-inflate; deflate-skip; ij⇿p⇒i≢j; _≤ₗₑₓ?_; ≤ₗₑₓ-total; ≤ₗₑₓ-antisym)
open import RoutingLib.Data.Path.UncertifiedI hiding (length)
open import RoutingLib.Data.Path.UncertifiedI.Properties

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Comparable as Comparable

open import RoutingLib.Routing.Protocols.BGPLite.Route
open import RoutingLib.Routing.Protocols.BGPLite.Policy using (Policy; apply; reject; apply-result)
open import RoutingLib.Routing.Protocols.BGPLite.Communities

module RoutingLib.Routing.Protocols.BGPLite.Algebra where

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
x@invalid        ⊕ y            = y
x                ⊕ y@invalid    = x
x@(valid l cs p) ⊕ y@(valid m ds q) with compare l m
... | tri< x<y _ _  = x
... | tri> _ _ y<x  = y
... | tri≈ _ x=y _  with compare (length p) (length q)
...   | tri< |p|<|q| _ _  = x
...   | tri> _ _ |q|<|p|  = y
...   | tri≈ _ |p|=|q| _  with p ≤ₗₑₓ? q
...     | yes p≤q = x
...     | no  q≤p = y

⊕-cong : Congruent₂ _≡_ _⊕_
⊕-cong = cong₂ _⊕_

infix 5 _▷_
_▷_ : ∀ {n} {i j : Fin n} → Step i j → Route → Route
_▷_ {_} {_} {_} _          invalid       = invalid
_▷_ {_} {i} {j} (step pol) (valid x c p) with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _    | _       = invalid
... | yes _    | yes _   = invalid
... | yes ij⇿p | no  i∈p = apply pol (valid x c ((toℕ i , toℕ j) ∷ p))

▷-cong : ∀ {n} {i j : Fin n} (f : Step i j) {r s} → r ≡ s → f ▷ r ≡ f ▷ s
▷-cong f refl = refl

f∞ : ∀ {n} (i j : Fin n) → Step i j
f∞ i j = step reject

f∞-reject : ∀ {n : ℕ} (i j : Fin n) (x : Route) → f∞ i j ▷ x ≡ invalid
f∞-reject i j invalid        = refl
f∞-reject i j (valid l cs p) with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _    | _       = refl
... | yes _    | yes _   = refl
... | yes ij⇿p | no  i∈p = refl

algebra : RawRoutingAlgebra _ _ _
algebra = record
  { Step               = Step
  ; Route              = Route
  ; _≈_                = _≡_
  ; _⊕_                = _⊕_
  ; _▷_                = _▷_
  ; 0#                 = 0#
  ; ∞                  = ∞
  ; f∞                 = f∞
  ; f∞-reject          = f∞-reject
  ; ≈-isDecEquivalence = ≡ᵣ-isDecEquivalence
  ; ▷-cong             = ▷-cong
  ; ⊕-cong             = ⊕-cong
  }


------------------
-- Path algebra --
------------------

path : Route → Path
path invalid       = invalid
path (valid _ _ p) = valid (deflate p)

r≈0⇒path[r]≈[] : ∀ {r} → r ≡ 0# → path r ≡ valid []
r≈0⇒path[r]≈[] refl = refl

r≈∞⇒path[r]≈∅ : ∀ {r} → r ≡ invalid → path r ≡ invalid
r≈∞⇒path[r]≈∅ refl = refl

path[r]≈∅⇒r≈∞ : ∀ {r} → path r ≡ invalid → r ≡ invalid
path[r]≈∅⇒r≈∞ {invalid}      refl = refl
path[r]≈∅⇒r≈∞ {valid l cs p} ()

path-reject : ∀ {n} {i j : Fin n} {r q} (f : Step i j) → path r ≡ valid q →
              (¬ (toℕ i , toℕ j) ⇿ᵥ q) ⊎ (toℕ i ∈ᵥₚ q) → f ▷ r ≡ invalid
path-reject {_} {i} {j} {invalid}      (step pol) pᵣ≈p inv = refl
path-reject {_} {i} {j} {valid l cs p} (step pol) refl inv with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _    | _       = refl
... | yes _    | yes _   = refl
... | yes ij⇿p | no  i∉p with inv
...   | inj₁ ¬ij⇿d[p] = contradiction ij⇿p {!!} --¬ij⇿p
...   | inj₂ i∈d[p]   = contradiction (∈-deflate⁻ i∈d[p]) i∉p

path-accept : ∀ {n} {i j : Fin n} {r q} (f : Step i j) → path r ≡ valid q → f ▷ r ≢ invalid →
              path (f ▷ r) ≡ valid ((toℕ i , toℕ j) ∷ q)
path-accept {_} {i} {j} {invalid}      {_} (step pol) pᵣ≈q f▷r≉0 = contradiction refl f▷r≉0
path-accept {_} {i} {j} {valid l cs p} {q} (step pol) eq f▷r≉0 with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no ¬e⇿p | _       = contradiction refl f▷r≉0
... | yes _   | yes i∈p = contradiction refl f▷r≉0
... | yes e⇿p | no  i∉p with apply-result pol l cs ((toℕ i , toℕ j) ∷ p)
...   | inj₁ ≡invalid = contradiction ≡invalid f▷r≉0
...   | inj₂ (k , ds , m , l≤k , ≡valid) = begin
  path (apply pol (valid l cs ((toℕ i , toℕ j) ∷ p))) ≡⟨ cong path ≡valid ⟩
  path (valid k ds (inflate ((toℕ i , toℕ j) ∷ p) m)) ≡⟨⟩
  valid (deflate (inflate ((toℕ i , toℕ j) ∷ p) m))   ≡⟨ cong valid (deflate-inflate _ m) ⟩
  valid (deflate ((toℕ i , toℕ j) ∷ p))               ≡⟨ cong valid (deflate-skip p (ij⇿p⇒i≢j e⇿p)) ⟩
  valid ((toℕ i , toℕ j) ∷ deflate p)                 ≡⟨ cong (λ p → valid (_ ∷ p)) (valid-injective eq) ⟩
  valid ((toℕ i , toℕ j) ∷ q)                         ∎
  where open ≡-Reasoning

isPathAlgebra : IsPathAlgebra algebra
isPathAlgebra = record
  { path             = path
  ; path-cong        = cong path
  ; r≈0⇒path[r]≈[]   = r≈0⇒path[r]≈[]
  ; r≈∞⇒path[r]≈∅    = r≈∞⇒path[r]≈∅
  ; path[r]≈∅⇒r≈∞    = path[r]≈∅⇒r≈∞
  ; path-reject      = path-reject
  ; path-accept      = path-accept
  }

---------------------
-- Routing algebra --
---------------------

open Comparable algebra

x≡fv⇒p[x]≢[] : ∀ {k cs p} {n} {i j : Fin n} (f : Step i j) v →
               valid k cs p ≡ f ▷ v → p ≢ []
x≡fv⇒p[x]≢[] f          invalid        ()
x≡fv⇒p[x]≢[] {i = i} {j} (step pol) (valid l cs p) x≈fv with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _    | _       = contradiction x≈fv λ()
... | yes _    | yes _   = contradiction x≈fv λ()
... | yes ij⇿p | no  i∈p = {!!} --apply pol (valid l cs ((toℕ i , toℕ j) ∷ p))

x≡fv∧y≈gw⇒p≢q : ∀ {k l cs ds p q} {n} {i j m : Fin n} (f : Step i j) (g : Step i m) v w →
                valid k cs p ≡ f ▷ v → valid l ds q ≡ g ▷ w →
                j ≢ m → p ≢ q
x≡fv∧y≈gw⇒p≢q {i = i} {j} {m} f g invalid w () y≈gw j≢m
x≡fv∧y≈gw⇒p≢q {i = i} {j} {m} f g (valid l cs p) invalid x≈fv () j≢m
x≡fv∧y≈gw⇒p≢q {i = i} {j} {m} (step pol₁) (step pol₂) (valid l cs p) (valid k ds q) x≈fv y≈gw j≢m
  with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p | (toℕ i , toℕ m) ⇿ᵥ? q | toℕ i ∈ᵥₚ? q
... | no  _ | _     | _     | _     = contradiction x≈fv λ()
... | yes _ | yes _ | _     | _     = contradiction x≈fv λ()
... | yes _ | no  _ | no  _ | _     = contradiction y≈gw λ()
... | yes _ | no  _ | yes _ | yes _ = contradiction y≈gw λ()
... | yes _ | no  _ | yes _ | no  _ = {!!}

≎⇒path≢ : ∀ {k l cs ds p q} → k ≡ l → valid k cs p ≎ valid l ds q → p ≢ q
≎⇒path≢ refl (0∞# refl ())
≎⇒path≢ refl (∞0# () refl)
≎⇒path≢ refl (∞∞# () ())
≎⇒path≢ refl (0e# g w refl ≈gw) = x≡fv⇒p[x]≢[] g w ≈gw ∘ sym
≎⇒path≢ refl (e0# f v ≈fv refl) = x≡fv⇒p[x]≢[] f v ≈fv
≎⇒path≢ refl (∞e# g w () x)
≎⇒path≢ refl (e∞# f v x ())
≎⇒path≢ refl (ee# f g v w j≢k x≈fv y≈gw) = x≡fv∧y≈gw⇒p≢q f g v w x≈fv y≈gw j≢k

⊕-sel : Selective _≡_ _⊕_
⊕-sel invalid        invalid        = inj₁ refl
⊕-sel invalid        (valid m ds q) = inj₂ refl
⊕-sel (valid l cs p) invalid        = inj₁ refl
⊕-sel (valid l cs p) (valid m ds q) with compare l m
... | tri< _ _ _ = inj₁ refl
... | tri> _ _ _ = inj₂ refl
... | tri≈ _ _ _ with compare (length p) (length q)
...   | tri< _ _ _  = inj₁ refl
...   | tri> _ _ _  = inj₂ refl
...   | tri≈ _ _ _  with p ≤ₗₑₓ? q
...     | yes p≤q = inj₁ refl
...     | no  q≤p = inj₂ refl

⊕-assoc : Associative _≡_ _⊕_
⊕-assoc x y z = {!!} --Choice.⊓-assoc

⊕-comm : ComparablyCommutative _≡_ _⊕_
⊕-comm {invalid}      {invalid}      x≎y = refl
⊕-comm {invalid}      {valid l cs p} x≎y = refl
⊕-comm {valid l cs p} {invalid}      x≎y = refl
⊕-comm {valid l cs p} {valid k ds q} x≎y with compare l k | compare k l
... | tri< _   _ _ | tri> _ _ _   = refl
... | tri< l<k _ _ | tri≈ _ _ l≮k = contradiction l<k l≮k
... | tri< l<k _ _ | tri< _ _ l≮k = contradiction l<k l≮k
... | tri> _   _ _ | tri< _ _ _   = refl
... | tri> _ _ k<l | tri≈ k≮l _ _ = contradiction k<l k≮l
... | tri> _ _ k<l | tri> k≮l _ _ = contradiction k<l k≮l
... | tri≈ _ l≡k _ | tri< _ k≢l _ = contradiction (sym l≡k) k≢l
... | tri≈ _ l≡k _ | tri> _ k≢l _ = contradiction (sym l≡k) k≢l
... | tri≈ _ l≡k _ | tri≈ _ _ _   with compare (lengthᵥ p) (lengthᵥ q) | compare (lengthᵥ q) (lengthᵥ p)
...   | tri< _ _ _       | tri> _ _ _       = refl
...   | tri< |p|<|q| _ _ | tri≈ _ _ |p|≮|q| = contradiction |p|<|q| |p|≮|q|
...   | tri< |p|<|q| _ _ | tri< _ _ |p|≮|q| = contradiction |p|<|q| |p|≮|q|
...   | tri> _ _ _       | tri< _ _ _       = refl
...   | tri> _ _ |q|<|p| | tri≈ |q|≮|p| _ _ = contradiction |q|<|p| |q|≮|p|
...   | tri> _ _ |q|<|p| | tri> |q|≮|p| _ _ = contradiction |q|<|p| |q|≮|p|
...   | tri≈ _ |p|≡|q| _ | tri< _ |q|≢|p| _ = contradiction (sym |p|≡|q|) |q|≢|p|
...   | tri≈ _ |p|≡|q| _ | tri> _ |q|≢|p| _ = contradiction (sym |p|≡|q|) |q|≢|p|
...   | tri≈ _ |p|≡|q| _ | tri≈ _ _ _       with p ≤ₗₑₓ? q | q ≤ₗₑₓ? p
...     | yes p≤q | yes q≤p = contradiction (≤ₗₑₓ-antisym p≤q q≤p) (≎⇒path≢ l≡k x≎y)
...     | yes p≤q | no  q≤p = refl
...     | no  p≰q | yes q≤p = refl
...     | no  p≰q | no  q≰p with ≤ₗₑₓ-total p q
...       | inj₁ p≤q = contradiction p≤q p≰q
...       | inj₂ q≤p = contradiction q≤p q≰p

⊕-identityʳ  : RightIdentity _≡_ invalid _⊕_
⊕-identityʳ invalid        = refl
⊕-identityʳ (valid l cs p) = refl

⊕-zeroʳ : RightZero _≡_ 0# _⊕_
⊕-zeroʳ invalid = refl
⊕-zeroʳ (valid l cs p) with compare l 0
... | tri< l<0 _ _ = contradiction l<0 λ()
... | tri> _   _ _ = refl
... | tri≈ _   _ _ with compare (length p) 0
...   | tri< |p|<0 _ _ = contradiction |p|<0 λ()
...   | tri> _     _ _ = refl
...   | tri≈ _     _ _ with p ≤ₗₑₓ? []
...     | yes []≤p = {!!}
...     | no  _    = refl

▷-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷ invalid ≡ invalid
▷-fixedPoint (step _) = refl

{-
isRoutingAlgebra : IsRoutingAlgebra algebra
isRoutingAlgebra = record
  { ⊕-sel        = ⊕-sel
  ; ⊕-comm       = ⊕-comm
  ; ⊕-assoc      = ⊕-assoc
  ; ⊕-zeroʳ      = ⊕-zeroʳ
  ; ⊕-identityʳ  = ⊕-identityʳ
  ; ▷-fixedPoint = ▷-fixedPoint
  }

----------------------
-- Other properties --
----------------------

isIncreasing : IsIncreasing algebra
isIncreasing {_} {_} {_} f          invalid        = refl
isIncreasing {_} {i} {j} (step pol) (valid l cs p) with (toℕ i , toℕ j) ⇿ᵥ? p | toℕ i ∈ᵥₚ? p
... | no  _   | _       = refl
... | yes _   | yes _   = refl
... | yes i⇿p | no  i∉p = {!!}
{-
with ≤ᵣ-total (apply pol (valid l cs ((toℕ i , toℕ j) ∷ p))) (valid l cs p)
...   | inj₂ r≤e▷r = {!!} --refl
...   | inj₁ e▷r≤r = contradiction e▷r≤r (apply-nonDecreasing pol)
-}

{-
isIncreasingPathAlgebra : IsIncreasingPathAlgebra algebra
isIncreasingPathAlgebra = record
  { isPathAlgebra = isPathAlgebra
  ; isIncreasing  = isIncreasing
  }
-}
-}
