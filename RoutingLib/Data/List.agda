open import Data.List hiding (downFrom)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _⊓_; _⊔_; _≤_; _<_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Function using (_∘_; id)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.List where

  -- stdlib
  max : ℕ → List ℕ → ℕ
  max ⊥ xs = foldr _⊔_ ⊥ xs

  -- stdlib
  min : ℕ → List ℕ → ℕ
  min ⊤ xs = foldr _⊓_ ⊤ xs

  -- stdlib
  dfilter : ∀ {a p} {A : Set a} {P : A → Set p} → Decidable P → List A → List A
  dfilter dec [] = []
  dfilter dec (x ∷ xs) with dec x
  ... | no  _ = dfilter dec xs
  ... | yes _ = x ∷ dfilter dec xs


  -----------
  -- Other --
  -----------

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

  -- Max and min

  index : ∀ {a} {A : Set a} (xs : List A) {i} → i < length xs → A
  index []       {_}     ()
  index (x ∷ xs) {zero}  (s≤s i<|xs|) = x
  index (x ∷ xs) {suc i} (s≤s i<|xs|) = index xs i<|xs|
