open import Data.Nat using (ℕ; _≟_; _+_; _≤_; zero; suc; s≤s)
open import Data.Nat.Properties using (_<?_; n≤m+n; ≤-refl; ≤-trans; n≮n; ≤⇒≯; n≤1+n; <⇒≯; <⇒≢)
open import Data.Fin using (fromℕ≤)
open import Data.Bool as 𝔹 using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Uncertified as Path using (Path; []; _∷_; length; deflate)
open import RoutingLib.Data.Path.Uncertified.Properties
open import RoutingLib.Data.Nat.Properties using (n≢1+n)

open import RoutingLib.Routing.Protocols.BGPLite.Route
open import RoutingLib.Routing.Protocols.BGPLite.Communities

module RoutingLib.Routing.Protocols.BGPLite.Policy where

------------------------------------------------------------------------
-- A language for writing conditional expressions

data Condition : Set where
  _and_     : Condition → Condition → Condition
  _or_      : Condition → Condition → Condition
  not       : Condition → Condition
  inPath    : (i : ℕ)         → Condition
  inComm    : (c : Community) → Condition
  isLevel   : (l : Level)     → Condition

evaluate : Condition → Route → Bool
evaluate (s and t)   r              = evaluate s r ∧ evaluate t r
evaluate (s or t)    r              = evaluate s r ∨ evaluate t r
evaluate (not s)     r              = 𝔹.not (evaluate s r)
evaluate (inComm  c) (valid l cs p) = c ∈? cs
evaluate (isLevel k) (valid l cs p) = ⌊ k ≟ l ⌋
evaluate (inPath  i) (valid l cs p) = ⌊ i ∈ₚ? p ⌋
evaluate (inComm  c) invalid        = false
evaluate (isLevel k) invalid        = false
evaluate (inPath  i) invalid        = false

------------------------------------------------------------------------
-- A language for writing policies

data Policy : Set₁ where
  reject   : Policy
  if_then_ : Condition → Policy → Policy
  compose  : Policy → Policy → Policy
  raise    : ℕ → Policy
  inflate  : ℕ → Policy
  addComm  : (c : Community) → Policy
  delComm  : (c : Community) → Policy

apply : Policy → Route → Route
apply _                   invalid        = invalid
apply (raise x)           (valid l cs p) = valid (x + l) cs p
apply (addComm c)         (valid l cs p) = valid l (add c cs) p
apply (delComm c)         (valid l cs p) = valid l (remove c cs) p
apply (inflate n)         (valid l cs p) = valid l cs (Path.inflate p n)
apply reject              r              = invalid
apply (compose pol₂ pol₁) r              = apply pol₁ (apply pol₂ r )
apply (if p then pol)     r              = if (evaluate p r) then (apply pol r) else r

apply-increasing : ∀ pol {l cs p k ds q} → apply pol (valid l cs p) ≡ valid k ds q →
                   l ≤ k × length p ≤ length q × deflate p ≡ deflate q
apply-increasing reject        ()
apply-increasing (raise x)     refl = n≤m+n x _ , ≤-refl , refl
apply-increasing (addComm c)   refl = ≤-refl    , ≤-refl , refl
apply-increasing (delComm c)   refl = ≤-refl    , ≤-refl , refl
apply-increasing (inflate n)   refl = ≤-refl    , inflate-length _ n , deflate-inflate _ n
apply-increasing (if x then pol) {l} {cs} {p} eq with evaluate x (valid l cs p) | eq
... | 𝔹.true  | e    = apply-increasing pol e
... | 𝔹.false | refl = ≤-refl , ≤-refl , refl
apply-increasing (compose r s) {l} {cs} {p} eq
  with apply r (valid l cs p) | inspect (apply r) (valid l cs p)
... | invalid | _ = contradiction eq λ()
... | valid j es o | [ eq′ ] with apply-increasing r eq′ | apply-increasing s eq
...   | (l≤j , |p|≤|o| , d[p]≡d[o]) | (j≤k , |o|≤|q| , d[o]≡d[q]) =
  ≤-trans l≤j j≤k , ≤-trans |p|≤|o| |o|≤|q| , trans d[p]≡d[o] d[o]≡d[q]

apply-nonDecreasing : ∀ pol {l cs e p} →
                      apply pol (valid l cs (e ∷ p)) ≰ᵣ valid l cs p
apply-nonDecreasing pol {l} {cs} {e} {p} leq
  with apply pol (valid l cs (e ∷ p)) | inspect (apply pol) (valid l cs (e ∷ p))
... | invalid      | _      = contradiction leq λ()
... | valid k ds q | [ eq ] with apply-increasing pol eq
...   | l≤k , |p|<|q| , _ with leq
...     | (level< k<l)          = contradiction k<l (≤⇒≯ l≤k)
...     | (length< _ 2+|p|<|p|) = contradiction 2+|p|<|p| (<⇒≯ |p|<|q|)
...     | (plex< _ 1+|p|≡|p| _) = contradiction 1+|p|≡|p| (<⇒≢ |p|<|q| ∘ sym)
...     | (comm≤ _ e∷p≈p _)     = contradiction e∷p≈p (|p|≢|q|⇒p≉q (<⇒≢ |p|<|q| ∘ sym))
