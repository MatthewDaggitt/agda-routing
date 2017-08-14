open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat
open import Data.List using (List; concat)
open import Data.Product using (∃₂)
open import Relation.Unary using (Pred)
open import Algebra.FunctionProperties using (Op₂)
open import Function using (_∘_)

open import RoutingLib.Data.List using (tabulate)
import RoutingLib.Data.Table as Table

module RoutingLib.Data.Matrix where
    
  Matrix : ∀ {a} → Set a → ℕ → ℕ → Set a
  Matrix A m n = Fin m → Fin n → A

  SquareMatrix : ∀ {a} → Set a → ℕ → Set a
  SquareMatrix A n = Matrix A n n
  
  -- Predicates

  All : ∀ {a ℓ} {A : Set a} → Pred A ℓ → ∀ {m n} → Pred (Matrix A m n) ℓ
  All P M = ∀ i j → P (M i j)

  Any : ∀ {a ℓ} {A : Set a} → Pred A ℓ → ∀ {m n} → Pred (Matrix A m n) ℓ
  Any P M = ∃₂ λ i j → P (M i j)

  -- Operations

  toList : ∀ {a m n} {A : Set a} → Matrix A m n → List A
  toList M = concat (tabulate (λ i → Table.toList (M i)))

  add : ∀ {a} {A : Set a} → Op₂ A → ∀ {m n} → Op₂ (Matrix A m n)
  add _⊕_ M N i j = M i j ⊕ N i j

  map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) →
        ∀ {m n} → Matrix A m n → Matrix B m n
  map f M i j = f (M i j)
  
{-
  multiply : ∀ {a} {A : Set a} → Op₂ A → ∀ {n} → Op₂ (Matrix A n)
  multiply _⊕_ M N i j = {!!}
-}

  zipWith : ∀ {a b c m n} {A : Set a} {B : Set b} {C : Set c} →
            (A → B → C) → Matrix A m n → Matrix B m n → Matrix C m n
  zipWith f M N i j = f (M i j) (N i j)

  foldʳᵈ : ∀ {a b} {A : Set a} {B : Set b} →
           (A → B → B) → B → ∀ {m n} → Matrix A m n → B
  foldʳᵈ f e {zero}  M = e
  foldʳᵈ f e {suc m} M = foldʳᵈ f (Table.foldr f e (M fzero)) (M ∘ fsuc)

  foldʳᵈ+ : ∀ {a} {A : Set a} → Op₂ A → ∀ {m n} → Matrix A (suc m) (suc n) → A
  foldʳᵈ+ _•_ M = foldʳᵈ _•_ (Table.foldr+ _•_ (M fzero)) (M ∘ fsuc)

  max+ : ∀ {m n} → Matrix ℕ (suc m) (suc n) → ℕ
  max+ M = foldʳᵈ+ _⊔_ M

  min+ : ∀ {m n} → Matrix ℕ (suc m) (suc n) → ℕ
  min+ M = foldʳᵈ+ _⊓_ M
