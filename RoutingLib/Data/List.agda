open import Data.List hiding (downFrom)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _⊓_; _⊔_; _≤_; _<_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Function using (_∘_; id)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.List where

  -- stdlib
  applyUpTo : ∀ {a} {A : Set a} (f : ℕ → A) n → List A
  applyUpTo f zero    = []
  applyUpTo f (suc n) = f zero ∷ applyUpTo (f ∘ suc) n

  -- stdlib
  applyDownFrom : ∀ {a} {A : Set a} (f : ℕ → A) n → List A
  applyDownFrom f zero    = []
  applyDownFrom f (suc n) = f n ∷ applyDownFrom f n

  -- stdlib
  upTo : ∀ n → List ℕ
  upTo = applyUpTo id

  -- stdlib
  downFrom : ∀ n → List ℕ
  downFrom = applyDownFrom id

  -- stdlib
  tabulate : ∀ {a n} {A : Set a} (f : Fin n → A) → List A
  tabulate {_} {zero}  f = []
  tabulate {_} {suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

  -- stdlib
  allFin : ∀ n → List (Fin n)
  allFin n = tabulate id


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

  max : ℕ → List ℕ → ℕ
  max ⊥ xs = foldr _⊔_ ⊥ xs

  min : ℕ → List ℕ → ℕ
  min ⊤ xs = foldr _⊓_ ⊤ xs

  dfilter : ∀ {a p} {A : Set a} {P : A → Set p} → Decidable P → List A → List A
  dfilter dec [] = []
  dfilter dec (x ∷ xs) with dec x
  ... | no  _ = dfilter dec xs
  ... | yes _ = x ∷ dfilter dec xs

  index : ∀ {a} {A : Set a} (xs : List A) {i} → i < length xs → A
  index []       {_}     ()
  index (x ∷ xs) {zero}  (s≤s i<|xs|) = x
  index (x ∷ xs) {suc i} (s≤s i<|xs|) = index xs i<|xs|
