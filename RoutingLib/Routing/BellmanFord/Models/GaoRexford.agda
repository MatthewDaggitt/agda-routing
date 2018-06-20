open import Data.Nat using (ℕ)

module RoutingLib.Routing.BellmanFord.Models.GaoRexford (n : ℕ) where

open import Level using () renaming (zero to ℓ₀)
open import Data.Nat using (ℕ; _≟_; _+_; _≤_; _<_)
open import Data.Nat.Properties using (_<?_; m≤m+n; ≤-refl; ≤-trans; <-cmp)
open import Data.Fin using (Fin; fromℕ≤)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_; if_then_else_)
open import Data.Product using (_,_; _×_)
open import Data.Maybe using (Maybe; nothing; just)
open import Function using (_∘_)
open import Relation.Binary using (Rel; Reflexive; Decidable; tri<; tri>; tri≈)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.SimplePath using (SimplePath; valid; invalid)
open import RoutingLib.Data.SimplePath.NonEmpty
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality using (_≈ₚ_; ≈ₚ-sym)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties using (∉-resp-≈ₚ; _⇿?_; _∉?_) renaming (_∈?_ to _∈ₚ?_)
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Lex using (<ₗₑₓ-cmp)

import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route as Routes
import RoutingLib.Routing.BellmanFord.Models.BGPLite.Route.Properties as RouteProperties
open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Communities

postulate levelOf : Fin n → ℕ



LocalPref : Set
LocalPref = ℕ

ASPath : Set
ASPath = SimplePathⁿᵗ n

ASLevel : Set
ASLevel = ℕ

RouteData : Set
RouteData = ASPath × LocalPref × CommunitySet

data Condition : Set where
  and      : Condition  → Condition  → Condition
  or       : Condition  → Condition  → Condition
  not      : Condition  → Condition
  inPath   : ℕ          → Condition
  inComm   : Community  → Condition

evaluate : Condition → RouteData → Bool
evaluate (and s t)   rd = evaluate s rd ∧ evaluate t rd
evaluate (or  s t)   rd = evaluate s rd ∨ evaluate t rd
evaluate (not s)     rd = 𝔹.not (evaluate s rd)
evaluate (inComm  c) (_ , _ , cs) = c ∈? cs
evaluate (inPath  i) (p , _ , _) with i <? n
... | no  _   = 𝔹.false
... | yes i<n = ⌊ fromℕ≤ i<n ∈ₚ? p ⌋

data Policy : Set₁ where
  reject       : Policy
  conditional  : Condition → Policy → Policy
  compose      : Policy → Policy → Policy
  setLocalPref : ℕ → Policy
  addCommunity : Community → Policy
  delCommunity : Community → Policy


apply : Policy → Maybe RouteData → Maybe RouteData
apply _                   nothing         = nothing
apply reject              _               = nothing
apply (setLocalPref x)    (just (p , l , cs)) = just (p , x , cs)
apply (addCommunity c)    (just (p , l , cs)) = just (p , l , add c cs)
apply (delCommunity c)    (just (p , l , cs)) = just (p , l , remove c cs)
apply (compose pol₂ pol₁) rd              = apply pol₁ (apply pol₂ rd)
apply (conditional c pol) (just rd)       = if (evaluate c rd) then (apply pol (just rd)) else (just rd)





data ASRelation : Set where
  cust : ASRelation
  peer : ASRelation
  prov : ASRelation

data _≈ₐₛᵣ_ : Rel ASRelation ℓ₀ where
  custEq : cust ≈ₐₛᵣ cust
  peerEq : peer ≈ₐₛᵣ peer
  provEq : prov ≈ₐₛᵣ prov

flip : ASRelation → ASRelation
flip cust = prov
flip peer = peer
flip prov = cust

data POData : Set where
  self  : POData
  other : ASRelation → ASLevel → POData

ASData : Set
ASData = ASLevel × ASRelation × ASPath


data ASRelationship (i j : Fin n) : Set where
  peerToPeer : ASRelationship i j
  custToProv : levelOf i < levelOf j → ASRelationship i j
  provToCust : levelOf j < levelOf i → ASRelationship i j

first : ∀ {i j} → ASRelationship i j → ASRelation
first peerToPeer     = peer
first (custToProv _) = cust
first (provToCust _) = prov

second : ∀ {i j} → ASRelationship i j → ASRelation
second peerToPeer     = peer
second (custToProv _) = prov
second (provToCust _) = cust

data EdgeWeight : Set₁ where
  edge : ∀ i j → ASRelationship i j → Policy → EdgeWeight

data Route : Set where
  invalid : Route
  valid   : ASRelation × RouteData → Route

data CanExport_To_ : ASRelation → ASRelation → Set where
  custToCust : CanExport cust To cust
  custToPeer : CanExport cust To peer
  custToProv : CanExport cust To prov
  peerToCust : CanExport peer To cust
  provToCust : CanExport prov To cust

CanExport_To?_ : Decidable CanExport_To_
CanExport cust To? cust = yes custToCust
CanExport cust To? peer = yes custToPeer
CanExport cust To? prov = yes custToProv
CanExport peer To? cust = yes peerToCust
CanExport peer To? peer = no (λ ())
CanExport peer To? prov = no (λ ())
CanExport prov To? cust = yes provToCust
CanExport prov To? peer = no (λ ())
CanExport prov To? prov = no (λ ())

F : EdgeWeight → Route → Route
F (edge i j r pol) invalid = invalid
F (edge i j r pol) (valid (s , p , l , cs)) with CanExport s To? second r
... | no  _ = invalid
... | yes _ with (i , j) ⇿? p | i ∉? p
...   | no  _   | _       = invalid
...   | yes _   | no  _   = invalid
...   | yes i⇿p | yes i∉p with apply pol (just ((i , j) ∷ p ∣ i⇿p ∣ i∉p , l , cs))
...     | nothing    = invalid
...     | just newRD = valid (first r , newRD)


infix 5 _⊕_
_⊕_ : Route → Route → Route
r₁                    ⊕ invalid               = r₁
invalid               ⊕ r₂                    = r₂
r₁@(valid (cust , _)) ⊕ r₂@(valid (peer , _)) = r₁
r₁@(valid (peer , _)) ⊕ r₂@(valid (cust , _)) = r₂
r₁@(valid (cust , _)) ⊕ r₂@(valid (prov , _)) = r₁
r₁@(valid (prov , _)) ⊕ r₂@(valid (cust , _)) = r₂
r₁@(valid (_    , p , l , _)) ⊕ r₂@(valid (_ , q , k , _)) with <-cmp l k
... | tri< l<k _ _ = r₁
... | tri> _ _ k<l = r₂
... | tri≈ _ l≡k _ with <-cmp (length p) (length q)
...   | tri< |p|<|q| _ _ = r₁
...   | tri> _ _ |q|<|p| = r₂
...   | tri≈ _ |p|≡|q| _ with <ₗₑₓ-cmp p q
...     | tri< p<ₗq _ _ = r₁
...     | tri> _ _ q<ₗp = r₂
...     | tri≈ _ p≈q _  = {!!}

infix 4 _≈ᵣ_
data _≈ᵣ_ : Rel Route ℓ₀ where
  invalidEq : invalid ≈ᵣ invalid
  validEq   : ∀ {l k p q r₁ r₂ cs₁ cs₂} → r₁ ≈ₐₛᵣ r₂ → l ≡ k → p ≈ₚ q → valid (r₁ , p , l , cs₁) ≈ᵣ valid (r₂ , q , k , cs₂)

≈ᵣ-refl : Reflexive _≈ᵣ_
≈ᵣ-refl = {!!}

F-increasing : ∀ e r → F e r ⊕ r ≈ᵣ r
F-increasing (edge i j r pol) invalid = ≈ᵣ-refl
F-increasing (edge i j r pol) (valid (s , p , l , cs)) with CanExport s To? second r
... | no  _   = ≈ᵣ-refl
... | yes s↠r with (i , j) ⇿? p | i ∉? p
...   | no  _   | _       = ≈ᵣ-refl
...   | yes _   | no  _   = ≈ᵣ-refl
...   | yes i⇿p | yes i∉p with apply pol (just ((i , j) ∷ p ∣ i⇿p ∣ i∉p , l , cs))
...     | nothing    = ≈ᵣ-refl
...     | just newRD with s | r | s↠r
...       | cust | provToCust _ | _ = ≈ᵣ-refl
...       | cust | peerToPeer   | _ = ≈ᵣ-refl
...       | peer | peerToPeer   | ()
...       | prov | peerToPeer   | ()
...       | peer | custToProv _ | ()
...       | prov | custToProv _ | ()
...       | peer | provToCust _ | _ = {!!} --() -- Neccesary
...       | prov | provToCust _ | _ = {!!} --() -- Neccesary
...       | cust | custToProv _ | _ = {!!} -- ≈ᵣ-refl
