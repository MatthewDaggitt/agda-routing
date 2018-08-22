open import Data.Fin using (Fin; zero; suc; fromℕ≤)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _≤?_)
open import Data.Nat.Properties using (_<?_; ≰⇒>)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.Fin.Properties using (fromℕ≤-injective)
open import RoutingLib.Data.Nat.Properties using (m<n⇒m≤1+n)
open import RoutingLib.Data.VertexPath.NonEmpty
open import RoutingLib.Data.VertexPath.NonEmpty.All
open import RoutingLib.Data.VertexPath.NonEmpty.Properties
open import RoutingLib.Data.Fin.Pigeonhole

module RoutingLib.Data.VertexPath.NonEmpty.Finiteness where

  -- Lookup functions
  
  lookup : ∀ p → Fin (length p) → ℕ
  lookup [ i ]       zero    = i
  lookup [ i ]       (suc ())
  lookup (i ∷ _ ∣ _) zero    = i
  lookup (_ ∷ p ∣ _) (suc k) = lookup p k

  -- Proofs
  
  ∉-lookup : ∀ {p k} → k ∉ p → ∀ l → k ≢ lookup p l 
  ∉-lookup {[ i ]}     (notThere i≢k)  zero    = i≢k
  ∉-lookup {[ i ]}     i∉p             (suc ())
  ∉-lookup {i ∷ p ∣ _} (notHere k≢i _) zero    = k≢i
  ∉-lookup {i ∷ p ∣ _} (notHere _ k∉p) (suc l) = ∉-lookup k∉p l
  
  lookup! : ∀ {p k l} → k ≢ l → lookup p k ≢ lookup p l
  lookup! {[ i ]}       {zero}   {zero}   0≢0 _ = 0≢0 refl
  lookup! {[ i ]}       {suc ()} {_}      k≢l
  lookup! {[ i ]}       {_}      {suc ()} k≢l
  lookup! {i ∷ p ∣ _}   {zero}   {zero}   0≢0 _ = 0≢0 refl
  lookup! {i ∷ p ∣ i∉p} {zero}   {suc l}  k≢l = ∉-lookup i∉p l
  lookup! {i ∷ p ∣ i∉p} {suc k}  {zero}   k≢l = ∉-lookup i∉p k ∘ sym
  lookup! {i ∷ p ∣ _}   {suc k}  {suc l}  k≢l = lookup! {p} (k≢l ∘ cong suc) 

  lookup-All : ∀ {p} {P : Pred ℕ p} {q} → All P q → ∀ i → P (lookup q i)
  lookup-All [ Pi ]    zero    = Pi
  lookup-All [ _  ]    (suc ())
  lookup-All (Pi ∷ _)  zero    = Pi
  lookup-All (_  ∷ Pq) (suc i) = lookup-All Pq i
  
  lookupᶠ : ∀ {n} {p : Pathⁿᵗ} → All (_< n) p → Fin (length p) → Fin n
  lookupᶠ p<n i = fromℕ≤ (lookup-All p<n i)

  lookupᶠ! : ∀ {n} {p : Pathⁿᵗ} (p<n : All (_< n) p) →
             ∀ {k l} → k ≢ l → lookupᶠ p<n k ≢ lookupᶠ p<n l
  lookupᶠ! p<n {k} {l} k≢l fromEq = lookup! k≢l (fromℕ≤-injective (lookup-All p<n k) (lookup-All p<n l) fromEq)
  
  |p|≤n : ∀ {n} {p : Pathⁿᵗ} → All (_< n) p → length p ≤ n
  |p|≤n {n} {p} p<n with length p ≤? n
  ... | yes |p|<n = |p|<n
  ... | no  |p|≮n with pigeonhole (≰⇒> |p|≮n) (lookupᶠ p<n)
  ...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookupᶠ! p<n i≢j)
  {-
  
  |p|≤1+n : ∀ {p n} → All (_< n) p → length p ≤ suc n
  |p|≤1+n {[]}          _   = z≤n
  |p|≤1+n {e ∷ p ∣ e∉p} p<n = m<n⇒m≤1+n (|p|<n p<n)
  -}
