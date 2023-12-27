--------------------------------------------------------------------------------
-- Agda routing library
--
-- A simple conditional policy language inspired by that of BGP. Policy
-- decisions can depend on any part of the path-weight, and hence decisions can
-- be made on its level, its communities and the path along which it was
-- generated.
--------------------------------------------------------------------------------

module RoutingLib.Routing.Protocols.BGPLite.Policies where

open import Data.Bool as 𝔹 using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Fin.Base using (toℕ)
open import Data.Nat using (ℕ; _≟_; _+_; _<ᵇ_; _≤ᵇ_; _∸_; _≤_; zero; suc; s≤s)
open import Data.Nat.Properties
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing.Basics.Path.Uncertified as Path
  using (Path; []; _∷_; length; deflate)
open import RoutingLib.Routing.Basics.Path.Uncertified.Properties

open import RoutingLib.Routing.Protocols.BGPLite.LocalPref
open import RoutingLib.Routing.Protocols.BGPLite.PathWeights
open import RoutingLib.Routing.Protocols.BGPLite.Communities

--------------------------------------------------------------------------------
-- A language for writing conditional expressions

data Condition : Set where
  _and_     : Condition → Condition → Condition
  _or_      : Condition → Condition → Condition
  not       : Condition → Condition
  inPath    : (i : ℕ)         → Condition
  inComm    : (c : Community) → Condition
  hasPref   : (l : LocalPref) → Condition

evaluate : Condition → PathWeight → Bool
evaluate (s and t)   r              = evaluate s r ∧ evaluate t r
evaluate (s or t)    r              = evaluate s r ∨ evaluate t r
evaluate (not s)     r              = 𝔹.not (evaluate s r)
evaluate (inComm  c) (valid l cs p) = c ∈? cs
evaluate (hasPref k) (valid l cs p) = ⌊ k ≟ˡᵖ l ⌋
evaluate (inPath  i) (valid l cs p) = ⌊ i ∈ₚ? p ⌋
evaluate (inComm  c) invalid        = false
evaluate (hasPref k) invalid        = false
evaluate (inPath  i) invalid        = false

--------------------------------------------------------------------------------
-- A language for writing policies

data Policy : Set₁ where
  reject     : Policy
  decrPrefBy : ℕ → Policy
  addComm    : (c : Community) → Policy
  delComm    : (c : Community) → Policy
  inflate    : ℕ → Policy
  if_then_   : Condition → Policy → Policy
  _⍮_       : Policy → Policy → Policy
  -- Note not a standard `;`. Use \; (7) instead

apply : Policy → PathWeight → PathWeight
apply _                   invalid        = invalid
apply (decrPrefBy x)      (valid l cs p) = valid (l - x) cs p
apply (addComm c)         (valid l cs p) = valid l (add c cs) p
apply (delComm c)         (valid l cs p) = valid l (remove c cs) p
apply (inflate n)         (valid l cs p) = valid l cs (Path.inflate p n)
apply reject              r              = invalid
apply (pol₂ ⍮ pol₁) r                    = apply pol₁ (apply pol₂ r )
apply (if p then pol)     r              = if (evaluate p r) then (apply pol r) else r

apply-result : ∀ pol l cs p → apply pol (valid l cs p) ≡ invalid ⊎
             ∃₂ λ k ds → ∃ λ i → l ≥ˡᵖ k × apply pol (valid l cs p) ≡ valid k ds (Path.inflate p i)
apply-result reject             l cs p = inj₁ refl
apply-result (decrPrefBy x)     l cs p = inj₂ (l - x , cs , 0 , l-x≤l l x , refl)
apply-result (inflate n)        l cs p = inj₂ (l     , cs          , n , ≤-refl    , refl)
apply-result (addComm c)        l cs p = inj₂ (l     , add    c cs , 0 , ≤-refl    , refl)
apply-result (delComm c)        l cs p = inj₂ (l     , remove c cs , 0 , ≤-refl    , refl)
apply-result (if c then pol)    l cs p with evaluate c (valid l cs p)
... | true  = apply-result pol l cs p
... | false = inj₂ (l , cs , 0 , ≤-refl , refl)
apply-result (pol₁ ⍮ pol₂) l cs p with apply-result pol₁ l cs p
... | inj₁ eq₁ rewrite eq₁         = inj₁ refl
... | inj₂ (k , ds , i , l≤k , eq₁) with apply-result pol₂ k ds (Path.inflate p i)
...   | inj₁ eq₂ = inj₁ (trans (cong (apply pol₂) eq₁) eq₂)
...   | inj₂ (m , es , j , k≤m , eq₂) = inj₂ (m , es , i + j , ≤-trans k≤m l≤k , (begin
  apply pol₂ (apply pol₁ (valid l cs p))         ≡⟨ cong (apply pol₂) eq₁ ⟩
  apply pol₂ (valid k ds (Path.inflate p i))     ≡⟨ eq₂ ⟩
  valid m es (Path.inflate (Path.inflate p i) j) ≡⟨ cong (valid m es) (inflate-inflate p i j) ⟩
  valid m es (Path.inflate p (i + j))            ∎))
  where open ≡-Reasoning
