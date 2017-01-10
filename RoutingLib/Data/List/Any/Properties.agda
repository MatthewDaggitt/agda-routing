open import Data.List using (_++_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Data.List using ([]; _∷_)
open import Data.List.Any using (Any; here; there)
open import Function using (id)

module RoutingLib.Data.List.Any.Properties where

  ++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = map there id (++⁻ xs p)
