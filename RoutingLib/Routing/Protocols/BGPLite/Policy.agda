open import Data.Nat using (ℕ; _≟_; _+_; _≤_; zero; suc; s≤s)
open import Data.Nat.Properties using (_<?_; n≤m+n; ≤-refl; ≤-trans; n≮n; ≤⇒≯; n≤1+n; <⇒≯)
open import Data.Fin using (fromℕ≤)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Uncertified using (_∷_)
open import RoutingLib.Data.Path.Uncertified.Properties using (∉ₚ-resp-≈ₚ; p≉i∷p; _∈ₚ?_)
open import RoutingLib.Data.Nat.Properties using (n≢1+n)

open import RoutingLib.Routing.Protocols.BGPLite.Route
open import RoutingLib.Routing.Protocols.BGPLite.Communities

module RoutingLib.Routing.Protocols.BGPLite.Policy where

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
evaluate true        _              = 𝔹.true
evaluate false       _              = 𝔹.false
evaluate (and s t)   r              = evaluate s r ∧ evaluate t r
evaluate (or  s t)   r              = evaluate s r ∨ evaluate t r
evaluate (not s)     r              = 𝔹.not (evaluate s r)
evaluate _           invalid        = 𝔹.false
evaluate (inComm  c) (valid l cs p) = c ∈? cs
evaluate (isLevel k) (valid l cs p) = ⌊ k ≟ l ⌋
evaluate (inPath  i) (valid l cs p) = ⌊ i ∈ₚ? p ⌋

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
...   | (l≤j , refl) | (j≤k , refl) = ≤-trans l≤j j≤k , refl

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
