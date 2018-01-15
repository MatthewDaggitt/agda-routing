open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.List hiding (downFrom)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _⊓_; _⊔_; _≤_; _<_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; id)
open import Relation.Binary using (Rel; Total)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.List where


  -- stdlib
  dfilter : ∀ {a p} {A : Set a} {P : A → Set p} → Decidable P → List A → List A
  dfilter dec [] = []
  dfilter dec (x ∷ xs) with dec x
  ... | no  _ = dfilter dec xs
  ... | yes _ = x ∷ dfilter dec xs


  -----------
  -- Other --
  -----------

  merge : ∀ {a ℓ} {A : Set a} {_≤_ : Rel A ℓ} → Total _≤_ → Op₂ (List A)
  merge total []       ys       = ys
  merge total xs       []       = xs
  merge total (x ∷ xs) (y ∷ ys) with total x y
  ... | inj₁ x≤y = x ∷ merge total xs (y ∷ ys)
  ... | inj₂ y≤x = y ∷ merge total (x ∷ xs) ys
  
  max : ℕ → List ℕ → ℕ
  max ⊥ xs = foldr _⊔_ ⊥ xs

  min : ℕ → List ℕ → ℕ
  min ⊤ xs = foldr _⊓_ ⊤ xs
  
  applyBetween : ∀ {a} {A : Set a} (f : ℕ → A) s e → List A
  applyBetween f s e = drop s (applyUpTo f e)

  between : ∀ s e → List ℕ
  between s e = applyBetween id s e


  combine : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
         → (A → B → C) → List A → List B → List C
  combine f [] _ = []
  combine f (x ∷ xs) ys = map (f x) ys ++ combine f xs ys

  allFinPairs : ∀ n → List (Fin n × Fin n)
  allFinPairs n = combine _,_ (allFin n) (allFin n)

  lookup : ∀ {a} {A : Set a} (xs : List A) {i} → i < length xs → A
  lookup []       {_}     ()
  lookup (x ∷ xs) {zero}  _            = x
  lookup (x ∷ xs) {suc i} (s≤s i<|xs|) = lookup xs i<|xs|
