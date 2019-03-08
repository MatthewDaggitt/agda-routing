open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (yes; no)

module RoutingLib.db716.Data.Path.VertexPath where

Vertex : ℕ → Set
Vertex = Fin

Path : ℕ → Set
Path n = List (Vertex n)

data AllPaths {n : ℕ} (i j : Fin n) (len : ℕ) : ℕ → Set where
  Root : ∀ {i j} → AllPaths i j len
  Branch : ∀ {l} → AllPaths (suc l) → Fin n → AllPaths l


--foldr : ∀ {b n len} {i j : Fin n} {B : Set b} → (A → B → B) → B → A
