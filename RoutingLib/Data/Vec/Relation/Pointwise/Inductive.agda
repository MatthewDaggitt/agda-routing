open import Algebra.FunctionProperties using (Op₂)
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec
open import Data.Vec.Relation.Pointwise.Inductive
open import Function using (_∘_)

open import RoutingLib.Data.Vec

module RoutingLib.Data.Vec.Relation.Pointwise.Inductive where

  foldr₂-All₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
             {_⊕ᵃ_ : Op₂ A} {_⊕ᵇ_ : Op₂ B} → 
             (∀ {w x y z} → P w x → P y z → P (w ⊕ᵃ y) (x ⊕ᵇ z)) →
             ∀ {n} {xs : Vec A n} {ys : Vec B n} {e₁} {e₂} → 
             P e₁ e₂ → Pointwise P xs ys → P (foldr₂ _⊕ᵃ_ e₁ xs) (foldr₂ _⊕ᵇ_ e₂ ys)
  foldr₂-All₂ P pres pe₁e₂ []            = pe₁e₂
  foldr₂-All₂ P pres pe₁e₂ (pxy ∷ pxsys) = pres pxy (foldr₂-All₂ P pres pe₁e₂ pxsys)

  tabulate-All₂ : ∀ {a b p} {A : Set a} {B : Set b}
                  (P : A → B → Set p) {n} {f : Fin n → A} {g : Fin n → B}
                  → (∀ i → P (f i) (g i))
                  → Pointwise P (tabulate f) (tabulate g)
  tabulate-All₂ P {zero} Pfg = []
  tabulate-All₂ P {suc n} Pfg = Pfg zero ∷ tabulate-All₂ P (Pfg ∘ suc)
