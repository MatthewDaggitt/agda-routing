open import Data.Nat using (ℕ)

module RoutingLib.Routing.BellmanFord.Models.GaoRexford (n : ℕ) where

open import Data.Nat using (ℕ; _≟_; _+_; _≤_)
open import Data.Nat.Properties using (_<?_; m≤m+n; ≤-refl; ≤-trans)
open import Data.Fin using (Fin; fromℕ≤)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_; if_then_else_)
open import Data.Product using (_,_; _×_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.SimplePath using (SimplePath; valid; invalid)
open import RoutingLib.Data.SimplePath.NonEmpty
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality using (≈ₚ-sym)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties using (∉-resp-≈ₚ; _⇿?_; _∉?_) renaming (_∈?_ to _∈ₚ?_)

import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route as Routes
import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route.Properties as RouteProperties
open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Communities





LocalPref : Set
LocalPref = ℕ

Level : Set
Level = ℕ

data Route : Set where
  invalid : Route
  valid   : LocalPref → Level → CommunitySet → SimplePathⁿᵗ n → Route

data Condition : Set where
  true     : Condition
  false    : Condition
  and      : Condition  → Condition  → Condition
  or       : Condition  → Condition  → Condition
  not      : Condition  → Condition
  inPath   : ℕ          → Condition
  inComm   : Community  → Condition
  isLevel  : Level      → Condition

data InnerPolicy : Set₁ where
  reject       : InnerPolicy
  conditional  : Condition → InnerPolicy → InnerPolicy
  compose      : InnerPolicy → InnerPolicy → InnerPolicy
  incrLocPref  : ℕ → InnerPolicy
  incrLevel    : ℕ → InnerPolicy
  addCommunity : Community → InnerPolicy
  delCommunity : Community → InnerPolicy

data Policy : Set₁ where
  pTp : ℕ → InnerPolicy → Policy
  cTp : ℕ → InnerPolicy → Policy


{-
evaluate : Condition → Route → Bool
evaluate true        _ = 𝔹.true
evaluate false       _ = 𝔹.false
evaluate (and s t)   r = evaluate s r ∧ evaluate t r
evaluate (or  s t)   r = evaluate s r ∨ evaluate t r
evaluate (not s)     r = 𝔹.not (evaluate s r)
evaluate _           invalid = 𝔹.false
evaluate (inComm  c) (valid x l cs p) = c ∈? cs
evaluate (isLevel k) (valid x l cs p) = ⌊ k ≟ l ⌋
evaluate (inPath  i) (valid x l cs p) with i <? n
... | no  _   = 𝔹.false
... | yes i<n = ⌊ fromℕ≤ i<n ∈ₚ? p ⌋

------------
-- Policy --
------------



data PeerToPeerPolicy : Set₁ where


apply : Policy → Route → Route
apply _              invalid         = invalid
apply reject         _               = invalid
apply (raise x)      (valid l cs p)  = valid (l + x) cs p
apply (addComm c)    (valid l cs p)  = valid l (add c cs) p
apply (delComm c)    (valid l cs p)  = valid l (remove c cs) p
apply (compose p q)  r               = apply q (apply p r)
apply (cond c  p)    r               = if (evaluate c r) then (apply p r) else r

F : (Fin n × Fin n × Policy) → Route → Route
F _              invalid        = invalid
F (i , j , pol)  (valid x c p)  with (i , j) ⇿? p | i ∉? p
... | no  _   | _      = invalid
... | yes _   | no  _  = invalid
... | yes i⇿p | yes i∉p with apply pol (valid x c p)
...   | invalid           = invalid
...   | (valid nl ncs _)  = valid nl ncs ((i , j) ∷ p ∣ i⇿p ∣ i∉p)

path : Route → SimplePath n
path invalid        = invalid
path (valid _ _ p)  = valid p
-}
