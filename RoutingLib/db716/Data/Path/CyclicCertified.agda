open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)

-- Certified Paths which may include cycles
module RoutingLib.db716.Data.Path.CyclicCertified where

Vertex : ℕ → Set
Vertex n = Fin n

Edge : ℕ → Set
Edge n = Vertex n × Vertex n

infix 4 _⇿_

data Path (n : ℕ) : Fin n → Fin n → Set
data _⇿_ {n : ℕ} : Edge n → Path n → Set

data Path n where
  [] : ∀ {i} → Path n i i
  _∷_ : ∀ {i j k} → ((i , j) : Edge n) (p : Path n j k) → Path n i k

data _⇿_ {n} where
  start : ∀ {i j} → (i , j) ⇿ []
  continue : ∀ {i j k p jk⇿p} → (i , j) ⇿ (j , k) ∷ p ∣ jk⇿p

