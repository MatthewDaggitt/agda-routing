open import Data.Nat using (ℕ; _≟_; _+_; _≤_; zero; suc; s≤s)
open import Data.Nat.Properties using (_<?_; n≤m+n; ≤-refl; ≤-trans; n≮n; ≤⇒≯; n≤1+n; <⇒≯)
open import Data.Fin using (fromℕ≤)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
-- open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PartialOrderReasoning as ≤-Reasoning

open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty using (_∷_)
open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty.Properties using (∉-resp-≈ₚ; p≉i∷p) renaming (_∈?_ to _∈ₚ?_)
open import RoutingLib.Data.Nat.Properties using (n≢1+n)

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
evaluate-cong (inPath  i) {valid _ _ p} {valid _ _ q} (validEq _ _ refl) with i <? n
... | no _    = refl
... | yes i<n with fromℕ≤ i<n ∈ₚ? p
...   | yes i∈p = refl
...   | no  i∉p = refl

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
apply (raise x)           (valid l cs p) = valid (x + l) cs p
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

apply-increasing : ∀ pol {l cs p k ds q} → apply pol (valid l cs p) ≡ valid k ds q → l ≤ k × p ≡ q
apply-increasing reject        ()
apply-increasing (raise x)     refl = n≤m+n x _ , refl
apply-increasing (addComm c)   refl = ≤-refl    , refl
apply-increasing (delComm c)   refl = ≤-refl    , refl
apply-increasing (cond x pol)  {l} {cs} {p} eq with evaluate x (valid l cs p) | eq
... | 𝔹.true  | e    = apply-increasing pol e
... | 𝔹.false | refl = ≤-refl , refl
apply-increasing (compose r s) {l} {cs} {p} eq
  with apply r (valid l cs p) | inspect (apply r) (valid l cs p)
... | invalid | _ = contradiction eq λ()
... | valid j es o | [ eq′ ] with apply-increasing r eq′ | apply-increasing s eq
...   | (l≤j , p≡o) | (j≤k , o≡q) = ≤-trans l≤j j≤k , trans p≡o o≡q

apply-nonDecreasing : ∀ pol {l cs e p} →
                      apply pol (valid l cs (e ∷ p)) ≰ᵣ valid l cs p
apply-nonDecreasing pol {l} {cs} {e} {p} leq
  with apply pol (valid l cs (e ∷ p)) | inspect (apply pol) (valid l cs (e ∷ p))
... | invalid      | _      = contradiction leq λ()
... | valid k ds q | [ eq ] with apply-increasing pol eq
...   | l≤k , refl with leq
...     | (level< k<l)          = contradiction k<l (≤⇒≯ l≤k)
...     | (length< _ 2+|p|<|p|) = contradiction 2+|p|<|p| (≤⇒≯ (n≤1+n _))
...     | (plex< _ 1+|p|≡|p| _) = contradiction 1+|p|≡|p| (n≢1+n _ ∘ sym)
...     | (comm≤ _ e∷p≈p _)     = contradiction e∷p≈p (p≉i∷p ∘ sym)
