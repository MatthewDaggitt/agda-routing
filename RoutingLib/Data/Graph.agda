
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

module RoutingLib.Data.Graph {a} where

  -- Structure

  Graph : ∀ (A : Set a) (n : ℕ) → Set a
  Graph A n = Fin n → Fin n → Maybe A
  

  -- Enumerations

  nodes : ∀ {A : Set a} {n : ℕ} → Graph A n → Vec (Fin n) n
  nodes {n = n} _ = allFin n

  possibleEdges : ∀ {A : Set a} {n : ℕ} → Graph A n → List (Fin n × Fin n)
  possibleEdges {n = n} _ = toList (allPairs (allFin n) (allFin n))

  actualEdges : ∀ {A : Set a} {n : ℕ} → Graph A n → List (Fin n × Fin n)
  actualEdges G = filter (λ {(i , j) → is-just (G i j)}) (possibleEdges G)


  -- Membership

  _ᵉ∈ᵍ_ : ∀ {A : Set a} {n : ℕ} → Fin n × Fin n → Graph A n → Set a
  (i , j) ᵉ∈ᵍ G = ∃ λ x → G i j ≡ just x
  
  _ᵉ∈ᵍ?_ : ∀ {A : Set a} {n : ℕ} → Decidable (_ᵉ∈ᵍ_ {A = A} {n})
  (i , j) ᵉ∈ᵍ? G with G i j
  ... | nothing = no  (λ {(v , ())})
  ... | just v  = yes (v , refl)

  ᵉ∈ᵍ-resp-≡ₗ : ∀ {A : Set a} {n : ℕ} {i j k} {G : Graph A n} → (i , j) ᵉ∈ᵍ G → j ≡ k → (i , k) ᵉ∈ᵍ G
  ᵉ∈ᵍ-resp-≡ₗ ij∈G refl = ij∈G
