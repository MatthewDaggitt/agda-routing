open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Fin.Subset using (Subset; ∣_∣)
open import Data.Nat
open import Data.List using (List; concat; tabulate)
open import Data.Product using (∃₂; _×_; _,_)
open import Level using (Level)
open import Relation.Unary using (Pred)
open import Algebra.Core using (Op₂)
open import Function using (_∘_)

open import Data.Vec.Functional as Vector using (Vector)
import RoutingLib.Data.Vec.Functional as Vector

module RoutingLib.Data.Matrix where

private
  variable
    a b c ℓ : Level
    A B C : Set a
    
Matrix : Set a → ℕ → ℕ → Set a
Matrix A m n = Fin m → Fin n → A

SquareMatrix : Set a → ℕ → Set a
SquareMatrix A n = Matrix A n n

-- Predicates

All : Pred A ℓ → ∀ {m n} → Pred (Matrix A m n) ℓ
All P M = ∀ i j → P (M i j)

Any : Pred A ℓ → ∀ {m n} → Pred (Matrix A m n) ℓ
Any P M = ∃₂ λ i j → P (M i j)

-- Operations

toList : ∀ {m n} → Matrix A m n → List A
toList M = concat (tabulate (λ i → Vector.toList (M i)))

map : (A → B) → ∀ {m n} → Matrix A m n → Matrix B m n
map f M i j = f (M i j)

zipWith : (A → B → C) → ∀ {m n} → Matrix A m n → Matrix B m n → Matrix C m n
zipWith f M N i j = f (M i j) (N i j)

fold : (A → B → B) → B → ∀ {m n} → Matrix A m n → B
fold f e M = Vector.foldr (λ t e → Vector.foldr f e t) e M

fold⁺ : Op₂ A → ∀ {m n} → Matrix A (suc m) (suc n) → A
fold⁺ _•_ {zero}  M = Vector.foldr⁺ _•_ (M zero)
fold⁺ _•_ {suc m} M = Vector.foldr⁺ _•_ (M zero) • fold⁺ _•_ (M ∘ suc)

max⁺ : ∀ {m n} → Matrix ℕ (suc m) (suc n) → ℕ
max⁺ M = fold⁺ _⊔_ M

min⁺ : ∀ {m n} → Matrix ℕ (suc m) (suc n) → ℕ
min⁺ M = fold⁺ _⊓_ M

row : ∀ {n} → Fin n → SquareMatrix A n → Vector A n 
row i M = M i

col : ∀ {n} → Fin n → SquareMatrix A n → Vector A n
col i M = λ j → M j i

_ᵀ : ∀ {n} → SquareMatrix A n → SquareMatrix A n
M ᵀ = λ i j → M j i
