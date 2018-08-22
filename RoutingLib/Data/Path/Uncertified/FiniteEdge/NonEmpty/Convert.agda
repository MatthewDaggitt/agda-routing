open import Data.Fin using (Fin; fromℕ≤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (Σ; _,_)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import RoutingLib.Data.Fin.Properties using (fromℕ≤-injective)
open import RoutingLib.Data.SimplePath.NonEmpty renaming (_∉_ to _∉ₛ_; _⇿_ to _⇿ₛ_)
open import RoutingLib.Data.Path.EdgePath.NonEmpty

module RoutingLib.Data.SimplePath.NonEmpty.Convert {n : ℕ} where

⇿-sub : ∀ {i j k} {p : SimplePathⁿᵗ n} → (i , j) ⇿ₛ p → k ≢ j → (k , j) ⇿ₛ p
⇿-sub (start _)    k≢j = start k≢j
⇿-sub (continue _) k≢j = continue k≢j

replaceSource : (p : SimplePathⁿᵗ n) → ∀ {k} → k ∉ₛ p → SimplePathⁿᵗ n
replaceSource []                         {_} _                   = []
replaceSource ((i , j) ∷ p ∣ ij⇿p ∣ i∉p) {k} (notHere _ k≢j k∉p) = (k , j) ∷ p ∣ ⇿-sub ij⇿p k≢j ∣ k∉p

replaceSource-∉ : ∀ {k l : Fin n} {p} (k∉p : k ∉ₛ p) → l ∉ₛ p → l ≢ k → l ∉ₛ replaceSource p k∉p
replaceSource-∉ notThere          notThere            l≢k = notThere
replaceSource-∉ (notHere _ _ k∉p) (notHere _ l≢j l∉p) l≢k = notHere l≢k l≢j l∉p

replaceSource-⇿ : ∀ {k : Fin n} {p} (k∉p : k ∉ₛ p) → {!!} ⇿ₛ replaceSource p k∉p
replaceSource-⇿ = {!!}


mutual

  to : Pathⁿᵗ → SimplePathⁿᵗ n
  to []                        = []
  to ((i , j) ∷ p ∣ e⇿p ∣ e∉p) with i <? n | j <? n
  ... | no  i≮n | _       = to p
  ... | yes i<n | no  j≮n = to p
  ... | yes i<n | yes j<n = (fromℕ≤ i<n , fromℕ≤ j<n) ∷ replaceSource (to p) {fromℕ≤ j<n} (to-∉ {p} j<n {!!}) ∣ {!replaceSource-⇿ ?!} ∣ {!!}
  
  to-⇿ : ∀ {p i j} (i<n : i < n) (j<n : j < n) → (i , j) ⇿ p → (fromℕ≤ i<n , fromℕ≤ j<n) ⇿ₛ to p
  to-⇿ {[]}                      i<n j<n (start i≢j) = start (i≢j ∘ fromℕ≤-injective i<n j<n)
  to-⇿ {(j , k) ∷ p ∣ e⇿p ∣ e∉p} i<n j<n (continue i≢j)  with j <? n | k <? n
  ... | no  j≮n  | _       = {!!} --to-⇿ i<n j<n {!!}
  ... | yes _    | no  k≮n = {!!} --to-⇿ i<n j<n {!!}
  ... | yes j<n' | yes k<n = {!!}

  to-∉ : ∀ {p i} (i<n : i < n) → i ∉ p → fromℕ≤ i<n ∉ₛ to p
  to-∉ {[]}                      i<n notThere              = notThere
  to-∉ {(j , k) ∷ p ∣ e⇿p ∣ e∉p} i<n (notHere i≢j i≢k i∉p) with j <? n | k <? n
  ... | no  _   | _       = {!!}
  ... | yes _   | no  _   = {!!}
  ... | yes j<n | yes k<n = {!!} --notHere (i≢j ∘ fromℕ≤-injective i<n j<n) (i≢k ∘ fromℕ≤-injective i<n k<n) (to-∉ {!!} i<n i∉p)

