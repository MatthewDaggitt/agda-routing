
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec using (Vec; allFin; toList)
open import Data.List using (List; filter)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Maybe using (Maybe; nothing; just; is-just)
open import Data.Vec using (allFin)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Vec using (allPairs)

module RoutingLib.Data.Graph where

  -- Structure

  Graph : ∀ {a} (A : Set a) (n : ℕ) → Set a
  Graph A n = Fin n → Fin n → Maybe A
  

  -- Enumerations

  nodes : ∀ {a} {A : Set a} {n : ℕ} → Graph A n → Vec (Fin n) n
  nodes {n = n} _ = allFin n

  possibleEdges : ∀ {a} {A : Set a} {n : ℕ} → Graph A n → List (Fin n × Fin n)
  possibleEdges {n = n} _ = toList (allPairs (allFin n) (allFin n))

  actualEdges : ∀ {a} {A : Set a} {n : ℕ} → Graph A n → List (Fin n × Fin n)
  actualEdges G = filter (λ {(i , j) → is-just (G i j)}) (possibleEdges G)


  -- Membership

  _ᵉ∈ᵍ_ : ∀ {a} {A : Set a} {n : ℕ} → Fin n × Fin n → Graph A n → Set a
  (i , j) ᵉ∈ᵍ G = ∃ λ x → G i j ≡ just x
  
  _ᵉ∈ᵍ?_ : ∀ {a} {A : Set a} {n : ℕ} → Decidable (_ᵉ∈ᵍ_ {A = A} {n})
  (i , j) ᵉ∈ᵍ? G with G i j
  ... | nothing = no  (λ {(v , ())})
  ... | just v  = yes (v , refl)
