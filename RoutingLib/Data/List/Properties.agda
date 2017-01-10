open import Level using () renaming (zero to lzero)
open import Data.Nat using (_≤_)
open import Data.List using (List; length; filter)
open import Data.List.Any as Any using (here; there)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (just; nothing)
open import Data.List.Properties using (length-gfilter)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl; setoid; _≡_; _≢_)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Any.GenericMembership using (∈-map)
open import RoutingLib.Data.List.All.Uniqueness using (Unique)
open import RoutingLib.Data.List.All.Uniqueness.Properties using ( map!)
open import RoutingLib.Data.List.All using ([]; _∷_)
open import RoutingLib.Data.List.All.Properties using (forced-map)

module RoutingLib.Data.List.Properties where

  open Any.Membership-≡

  ----------------------
  -- Pushed to stdlib --
  ----------------------

  length-filter : ∀ {a} {A : Set a} (p : A → Bool) xs → length (filter p xs) ≤ length xs
  length-filter p xs = length-gfilter (λ x → if p x then just x else nothing) xs


  ------------
  -- allFin --
  ------------

  Sᶠ : ∀ {n} → Setoid lzero lzero
  Sᶠ {n} = setoid (Fin n)

  private
    i≡j⇒i+1≡j+1 : ∀ {m} {i j : Fin m} → i ≡ j → fsuc i ≡ fsuc j
    i≡j⇒i+1≡j+1 refl = refl

    i≢j⇒i+1≢j+1 : ∀ {m} {i j : Fin m} → i ≢ j → fsuc i ≢ fsuc j
    i≢j⇒i+1≢j+1 {_} {i} {.i} i≢i refl = i≢i refl

  ∈-allFin : ∀ m n → n ∈ allFin m 
  ∈-allFin zero ()
  ∈-allFin (suc m) fzero = here refl
  ∈-allFin (suc m) (fsuc n) = there (∈-map Sᶠ Sᶠ i≡j⇒i+1≡j+1 (∈-allFin m n))    

  allFin! : ∀ n → Unique Sᶠ (allFin n)
  allFin! zero = []
  allFin! (suc n) = forced-map (λ _ → λ {()}) (allFin n) ∷ map! Sᶠ Sᶠ i≢j⇒i+1≢j+1 (allFin! n)
