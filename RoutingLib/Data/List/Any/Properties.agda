open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to mapₛ)
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.List.Any as Any using (Any; here; there)
open import Function using (id; _∘_; _$_)
open import Relation.Binary.PropositionalEquality using (refl)

open Any.Membership-≡ using (_∈_)

module RoutingLib.Data.List.Any.Properties where

  ++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = mapₛ there id (++⁻ xs p)

  map⁺ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
        {f : A → B} {xs} → Any (P ∘ f) xs → Any P (map f xs)
  map⁺ (here p)  = here p
  map⁺ (there p) = there $ map⁺ p
