open import Data.Nat using (ℕ; zero; suc; _⊔_; _⊓_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary using (Rel; REL)
open import Relation.Unary using (Pred)
open import Data.Product using (∃; _×_; _,_)
open import Data.List using (List)
open import Function using (_∘_)

open import RoutingLib.Data.List using (tabulate)

module RoutingLib.Data.Table where

  Table : ∀ {a} → Set a → ℕ → Set a
  Table A n = Fin n → A

  -- Predicates over tables
  
  All : ∀ {a ℓ} {A : Set a} → Pred A ℓ → ∀ {n} → Pred (Table A n) ℓ
  All P t = ∀ i → P (t i)

  Any : ∀ {a ℓ} {A : Set a} → Pred A ℓ → ∀ {n} → Pred (Table A n) ℓ
  Any P t = ∃ λ i → P (t i)

  -- Functions
  
  toList : ∀ {a n} {A : Set a} → Table A n → List A
  toList = tabulate

  map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → ∀{n} → Table A n → Table B n
  map f t i = f (t i)

  zipWith : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
            (A → B → C) → Table A n → Table B n → Table C n
  zipWith f t s i = f (t i) (s i)

  zip : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
        Table A n → Table B n → Table (A × B) n
  zip t s i = t i , s i

  -- Standard fold implementations
  
  foldr : ∀ {a b} {A : Set a} {B : Set b} →
          (A → B → B) → B → ∀ {n} → Table A n → B
  foldr f e {zero}  t = e
  foldr f e {suc n} t = f (t fzero) (foldr f e (t ∘ fsuc))

  foldr+ : ∀ {a} {A : Set a} → (A → A → A) → ∀ {n} → Table A (suc n) → A
  foldr+ f t = foldr f (t fzero) (t ∘ fsuc)
  
  foldl : ∀ {a b} {A : Set a} {B : Set b} →
          (B → A → B) → B → ∀ {n} → Table A n → B
  foldl f e {zero}  t = e
  foldl f e {suc n} t = foldl f (f e (t fzero)) (t ∘ fsuc)

  foldl+ : ∀ {a} {A : Set a} → (A → A → A) → ∀ {n} → Table A (suc n) → A
  foldl+ f t = foldl f (t fzero) (t ∘ fsuc)



  max+ : ∀ {n} → Table ℕ (suc n) → ℕ
  max+ t = foldr+ _⊔_ t

  min+ : ∀ {n} → Table ℕ (suc n) → ℕ
  min+ t = foldr+ _⊓_ t
