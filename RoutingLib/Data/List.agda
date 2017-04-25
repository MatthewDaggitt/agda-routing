open import Data.List hiding (downFrom)
open import Data.Nat using (ℕ; zero; suc; _⊓_; _⊔_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Function using (_∘_; id)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.List where

  applyUpTo : ∀ {a} {A : Set a} (f : ℕ → A) n → List A
  applyUpTo f zero    = []
  applyUpTo f (suc n) = f zero ∷ applyUpTo (f ∘ suc) n

  applyDownFrom : ∀ {a} {A : Set a} (f : ℕ → A) n → List A
  applyDownFrom f zero = []
  applyDownFrom f (suc n) = f n ∷ applyDownFrom f n

  upTo : ∀ n → List ℕ
  upTo = applyUpTo id

  downFrom : ∀ n → List ℕ
  downFrom = applyDownFrom id


  tabulate : ∀ {a n} {A : Set a} (f : Fin n → A) → List A
  tabulate {_} {zero}  f = []
  tabulate {_} {suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

  allFin : ∀ n → List (Fin n)
  allFin n = tabulate id


  combine : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
         → (A → B → C) → List A → List B → List C
  combine f [] _ = []
  combine f (x ∷ xs) ys = map (f x) ys ++ combine f xs ys



  -- Max and min

  max : List ℕ → ℕ
  max xs = foldr _⊔_ 0 xs

  min : List ℕ → ℕ
  min xs = foldr _⊓_ 0 xs


  decFilter : ∀ {a b} {A : Set a} {P : A → Set b} → Decidable P → List A → List A
  decFilter dec [] = []
  decFilter dec (x ∷ xs) with dec x
  ... | no  _ = decFilter dec xs
  ... | yes _ = x ∷ decFilter dec xs
