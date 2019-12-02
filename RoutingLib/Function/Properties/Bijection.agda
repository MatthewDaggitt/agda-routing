
module RoutingLib.Function.Properties.Bijection where

open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
open import Data.Product
open import Level

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    
refl : ∀ {S : Setoid a ℓ} → Bijection S S
refl {S = S} = record
  { f         = id
  ; cong      = id
  ; bijective = id , (λ x → x , Setoid.refl S)
  }

-- Can't prove full symmetry as we have no proof that the first projection of surjection
-- preserves equality
sym : ∀ {A : Set a} {T : Setoid b ℓ} → Bijection T (P.setoid A) → Bijection (P.setoid A) T
sym {T = T} bij = record
  { f         = g
  ; cong      = reflexive ∘ P.cong g
  ; bijective = (λ {x} {y} gx≈gy → P.trans (P.trans (P.sym (proj₂ (surjective x))) (cong gx≈gy)) (proj₂ (surjective y))) ,
                (λ x → f x , injective (proj₂ (surjective (f x))))
  } where open Bijection bij; g = proj₁ ∘ surjective; open Setoid T

