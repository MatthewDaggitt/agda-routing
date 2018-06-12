open import Data.Nat using (ℕ; _≟_; _+_; _≤_)
open import Data.Nat.Properties using (_<?_; m≤m+n; ≤-refl; ≤-trans)
open import Data.Fin using (fromℕ≤)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_; if_then_else_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality using (≈ₚ-sym)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties using (∉-resp-≈ₚ) renaming (_∈?_ to _∈ₚ?_)

import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route as Routes
import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route.Properties as RouteProperties
open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Communities

module RoutingLib.Routing.BellmanFord.Models.BGPLite.Policy (n : ℕ) where

open Routes n
open RouteProperties n

data Condition : Set where
  true    : Condition
  false   : Condition
  and     : Condition → Condition → Condition
  or      : Condition → Condition → Condition
  not     : Condition → Condition
  inPath  : (i : ℕ)         → Condition
  inComm  : (c : Community) → Condition
  isLevel : (l : Level)     → Condition

evaluate : Condition → Route → Bool
evaluate true        _ = 𝔹.true
evaluate false       _ = 𝔹.false
evaluate (and s t)   r = evaluate s r ∧ evaluate t r
evaluate (or  s t)   r = evaluate s r ∨ evaluate t r
evaluate (not s)     r = 𝔹.not (evaluate s r)
evaluate _           invalid = 𝔹.false
evaluate (inComm  c) (valid l cs p) = c ∈? cs
evaluate (isLevel k) (valid l cs p) = ⌊ k ≟ l ⌋
evaluate (inPath  i) (valid l cs p) with i <? n
... | no  _   = 𝔹.false
... | yes i<n = ⌊ fromℕ≤ i<n ∈ₚ? p ⌋

evaluate-cong : ∀ p {r s} → r ≈ᵣ s → evaluate p r ≡ evaluate p s
evaluate-cong true        r≈s = refl
evaluate-cong false       r≈s = refl
evaluate-cong (and p q)   r≈s = cong₂ _∧_ (evaluate-cong p r≈s) (evaluate-cong q r≈s)
evaluate-cong (or  p q)   r≈s = cong₂ _∨_ (evaluate-cong p r≈s) (evaluate-cong q r≈s)
evaluate-cong (not p)     r≈s = cong 𝔹.not (evaluate-cong p r≈s)
evaluate-cong (inPath  i) invalidEq = refl
evaluate-cong (inComm  c) invalidEq = refl
evaluate-cong (isLevel l) invalidEq = refl
evaluate-cong (inComm  c) (validEq _ cs≈ds _)   = ∈-resp-≈ᶜˢ c cs≈ds
evaluate-cong (isLevel l) (validEq refl _  _)   = refl
evaluate-cong (inPath  i) {valid _ _ p} {valid _ _ q} (validEq _    _  p≈q) with i <? n
... | no _    = refl
... | yes i<n with fromℕ≤ i<n ∈ₚ? p | fromℕ≤ i<n ∈ₚ? q
...   | yes i∈p | yes i∈q = refl
...   | yes i∈p | no  i∉q = contradiction (i∈p ∘ (∉-resp-≈ₚ (≈ₚ-sym p≈q))) i∉q
...   | no  i∉p | yes i∈q = contradiction (i∈q ∘ ∉-resp-≈ₚ p≈q) i∉p
...   | no  i∉p | no  i∉q = refl

------------
-- Policy --
------------

data Policy : Set₁ where
  reject     : Policy
  cond       : Condition → Policy → Policy
  compose    : Policy → Policy → Policy
  raise      : ℕ → Policy
  addComm    : (c : Community) → Policy
  delComm    : (c : Community) → Policy

apply : Policy → Route → Route
apply _                   invalid        = invalid
apply (raise x)           (valid l cs p) = valid (l + x) cs p
apply (addComm c)         (valid l cs p) = valid l (add c cs) p
apply (delComm c)         (valid l cs p) = valid l (remove c cs) p
apply reject              r              = invalid
apply (compose pol₂ pol₁) r              = apply pol₁ (apply pol₂ r )
apply (cond p pol)        r              = if (evaluate p r) then (apply pol r) else r

apply-cong : ∀ pol {r s} → r ≈ᵣ s → apply pol r ≈ᵣ apply pol s
apply-cong pol             invalidEq                = invalidEq
apply-cong (raise x)       (validEq refl cs≈ds p≈q) = validEq refl cs≈ds p≈q
apply-cong (addComm c)     (validEq k≡l cs≈ds p≈q)  = validEq k≡l (add-cong c cs≈ds) p≈q
apply-cong (delComm c)     (validEq k≡l cs≈ds p≈q)  = validEq k≡l (remove-cong c cs≈ds) p≈q
apply-cong reject          (validEq _   _     _)    = invalidEq
apply-cong (compose p₂ p₁) (validEq k≡l cs≈ds p≈q)  = apply-cong p₁ (apply-cong p₂ (validEq k≡l cs≈ds p≈q))
apply-cong (cond P? pol)    {r@(valid k cs p)} {s@(valid l ds q)} r≈s@(validEq k≡l cs≈ds p≈q)
  with evaluate P? r | evaluate P? s | inspect (evaluate P?) r | inspect (evaluate P?) s
... | 𝔹.true  | 𝔹.true  | _        | _        = apply-cong pol r≈s
... | 𝔹.true  | 𝔹.false | [ Pr≡t ] | [ Ps≡f ] =
  contradiction (trans (trans (sym Pr≡t) (evaluate-cong P? r≈s)) Ps≡f) λ()
... | 𝔹.false | 𝔹.true  | [ Pr≡f ] | [ Ps≡t ] =
  contradiction (trans (trans (sym Ps≡t) (sym (evaluate-cong P? r≈s))) Pr≡f) λ()
... | 𝔹.false | 𝔹.false | _        | _        = r≈s

apply-levelIncr : ∀ pol {l cs p k ds q} → apply pol (valid l cs p) ≈ᵣ valid k ds q → l ≤ k
apply-levelIncr reject              ()
apply-levelIncr (raise x)           (validEq refl _ _) = m≤m+n _ x
apply-levelIncr (addComm c)         (validEq refl _ _) = ≤-refl
apply-levelIncr (delComm c)         (validEq refl _ _) = ≤-refl
apply-levelIncr (compose pol₂ pol₁)  {l} {cs} {p} eq
  with apply pol₂ (valid l cs p) | inspect (apply pol₂) (valid l cs p)
... | invalid      | _         = contradiction eq λ()
... | valid m ds r | [ app≡u ] =
  ≤-trans (apply-levelIncr pol₂ (≈ᵣ-reflexive app≡u)) (apply-levelIncr pol₁ eq)
apply-levelIncr (cond P? pol) {l} {cs} {p} eq with evaluate P? (valid l cs p)
... | 𝔹.true  = apply-levelIncr pol eq
... | 𝔹.false with eq
...   | validEq refl _ _ = ≤-refl

apply-trans : ∀ pol {x y r s} → r ≈ᵣ s → apply pol r ≡ x → apply pol s ≡ y → x ≈ᵣ y
apply-trans pol r≈s refl refl = apply-cong pol r≈s
