
open import Algebra using (Semiring)

module RoutingLib.db716.Data.Path.UncertifiedFinite.Weights {c ℓ} (S : Semiring c ℓ) where

open import Data.Nat using (ℕ; suc; _≤_; s≤s; _⊓_) renaming (_*_ to _×ₙ_)
open import Data.Nat.Properties using (≰⇒>; n≤1+n; ≤-reflexive; <-trans)
open import Data.Fin using (Fin; inject₁; _≟_; punchOut; punchIn; _<_; _<?_; reduce≥) renaming (suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; ≤∧≢⇒<; inject₁-injective)
open import Data.List using (List; []; _∷_; _++_; foldl; foldr; map; concat; length; lookup; zip)
open import Data.List.Any using (Any; here; there; any; index) renaming (map to anymap)
open import Data.List.All using (All; []; _∷_; tabulate)
open import Data.List.Properties
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_; Pointwise-≡⇒≡) renaming (refl to ≈ₚ-refl)
open import Data.List.Membership.Propositional using (_∈_; find; mapWith∈; lose)
open import Data.List.Membership.Propositional.Properties using (∈-lookup; ∈-∃++)
open import Data.List.Membership.DecPropositional
open import Data.Product using (_×_; _,_; <_,_>; proj₁; proj₂; ∃; ∃₂)
open import Data.Product.Relation.Pointwise.NonDependent using (≡⇒≡×≡; ≡×≡⇒≡)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Algebra using (Semiring)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong₂) renaming (refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans)
open import RoutingLib.Data.Matrix.Relation.Binary.Equality using (_≈ₘ_)

open import RoutingLib.Data.Matrix using (SquareMatrix) renaming (map to matmap)
open import RoutingLib.db716.Algebra.SemiringMatrix S
open import RoutingLib.db716.Algebra.Properties.Summation S
open import RoutingLib.db716.Data.Matrix
open import RoutingLib.Data.Table using () renaming (foldr to tfoldr)

open import RoutingLib.db716.Data.Path.UncertifiedFinite

open Semiring S

edgeWeight : ∀ {n} → SquareMatrix Carrier n → Edge n → Carrier
edgeWeight M (i , j) = M i j

weight : ∀ {n} → SquareMatrix Carrier n → Path n → Carrier 
weight M p = foldr _*_ 1# (map (edgeWeight M) p)

private pow : ∀ {n} → SquareMatrix Carrier n → ℕ → SquareMatrix Carrier n
pow {n} = pow'
  where open import RoutingLib.db716.Algebra.Semiring (SemiringMat n) using () renaming (pow to pow')

data StartsWith : ∀ {n} → Path n → Fin n → Set where
  startsWith : ∀ {n} (p : Path n) (i : Fin n) {j : Fin n} → StartsWith ((i , j) ∷ p) i

-- Assumes _+_ "selects" the best weight from two paths
-- Can maybe find a better name for this because in some cases (eg flow problems) _+_ does not have to be selective
best-path-weight : ∀ {n} → SquareMatrix Carrier n → List (Path n) → Carrier
best-path-weight M l = foldr (λ p x → weight M p + x) 0# l
                                                         
accum : List Carrier → Carrier
accum = foldr _+_ 0#

accumFunc : ∀ {a} {A : Set a} → List A → (A → Carrier) → Carrier
accumFunc l f = foldr (λ a x → (f a) + x) 0# l

