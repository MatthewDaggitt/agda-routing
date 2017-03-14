open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec using (Vec; allFin; toList; allPairs)
open import Data.List using (List; filter)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Maybe using (Maybe; nothing; just; is-just)
open import Data.Vec using (allFin)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.Graph where

  -- Edges

  Edge : ℕ → Set lzero
  Edge n = Fin n × Fin n

  Connected : ∀ {n} → Edge n → Edge n → Set lzero
  Connected (i , j) (k , l) = j ≡ k

  NonTrivial : ∀ {n} → Edge n → Set lzero
  NonTrivial (i , j) = i ≢ j

  allEdges : ∀ (n : ℕ) → List (Edge n)
  allEdges n = toList (allPairs (allFin n) (allFin n))


  -- Graph

  Graph : ∀ {a} (A : Set a) (n : ℕ) → Set a
  Graph A n = Fin n → Fin n → Maybe A

  nodes : ∀ {a} {A : Set a} {n : ℕ} → Graph A n → Vec (Fin n) n
  nodes {n = n} _ = allFin n

  edges : ∀ {a} {A : Set a} {n : ℕ} → Graph A n → List (Edge n)
  edges {n = n} G = filter (λ {(i , j) → is-just (G i j)}) (allEdges n)


  -- Membership

  _∈_ : ∀ {a} {A : Set a} {n : ℕ} → Edge n → Graph A n → Set a
  (i , j) ∈ G = ∃ λ x → G i j ≡ just x

  _∈?_ : ∀ {a} {A : Set a} {n : ℕ} → Decidable (_∈_ {A = A} {n})
  (i , j) ∈? G with G i j
  ... | nothing = no  (λ {(v , ())})
  ... | just v  = yes (v , refl)

  ∈-resp-≡ₗ : ∀ {a} {A : Set a} {n : ℕ} {i j k} {G : Graph A n} → (i , j) ∈ G → j ≡ k → (i , k) ∈ G
  ∈-resp-≡ₗ ij∈G refl = ij∈G
