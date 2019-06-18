--------------------------------------------------------------------------------
-- Agda routing library
--
-- A simple conditional policy language inspired by that of BGP. Policy
-- decisions can depend on any part of the route, and hence decisions can be
-- made on its level, its communities and the path along which it was generated.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Policy where

open import Data.Bool as 𝔹 using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Fin using (fromℕ≤)
open import Data.Nat using (ℕ; _≟_; _+_; _≤_; zero; suc; s≤s)
open import Data.Nat.Properties
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Uncertified as Path
  using (Path; []; _∷_; length; deflate)
open import RoutingLib.Data.Path.Uncertified.Properties
open import RoutingLib.Data.Nat.Properties using (n≢1+n)

open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Route
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Communities

--------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------
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

apply-result : ∀ pol l cs p → apply pol (valid l cs p) ≡ invalid ⊎
             ∃₂ λ k ds → ∃ λ i → l ≤ k × apply pol (valid l cs p) ≡ valid k ds (Path.inflate p i)
apply-result reject             l cs p = inj₁ refl
apply-result (raise x)          l cs p = inj₂ (x + l , cs          , 0 , m≤n+m l x , refl)
apply-result (inflate n)        l cs p = inj₂ (l     , cs          , n , ≤-refl    , refl)
apply-result (addComm c)        l cs p = inj₂ (l     , add    c cs , 0 , ≤-refl    , refl)
apply-result (delComm c)        l cs p = inj₂ (l     , remove c cs , 0 , ≤-refl    , refl)
apply-result (if c then pol)    l cs p with evaluate c (valid l cs p)
... | true  = apply-result pol l cs p
... | false = inj₂ (l , cs , 0 , ≤-refl , refl)
apply-result (compose pol₁ pol₂) l cs p with apply-result pol₁ l cs p
... | inj₁ eq₁ rewrite eq₁         = inj₁ refl
... | inj₂ (k , ds , i , l≤k , eq₁) with apply-result pol₂ k ds (Path.inflate p i)
...   | inj₁ eq₂ = inj₁ (trans (cong (apply pol₂) eq₁) eq₂)
...   | inj₂ (m , es , j , k≤m , eq₂) = inj₂ (m , es , i + j , ≤-trans l≤k k≤m , (begin
  apply pol₂ (apply pol₁ (valid l cs p))         ≡⟨ cong (apply pol₂) eq₁ ⟩
  apply pol₂ (valid k ds (Path.inflate p i))     ≡⟨ eq₂ ⟩
  valid m es (Path.inflate (Path.inflate p i) j) ≡⟨ cong (valid m es) (inflate-inflate p i j) ⟩
  valid m es (Path.inflate p (i + j))            ∎))
  where open ≡-Reasoning
