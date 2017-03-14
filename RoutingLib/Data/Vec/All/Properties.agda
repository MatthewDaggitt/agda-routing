open import Data.Vec as Vec hiding (map; zip)
open import Data.Vec.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (zero; suc)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)
open import Relation.Binary using (_⇒_)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.Vec using (map; zip; foldr₂)
open import RoutingLib.Data.Vec.All using (All₂; []; _∷_)

module RoutingLib.Data.Vec.All.Properties where

  map-All : ∀ {a b p q} {A : Set a} {B : Set b} 
            (P : A → Set p) (Q : B → Set q) (f : A → B) → 
            P ⋐ Q ∘ f → 
            ∀ {n} {xs : Vec A n} → All P xs → All Q (map f xs)
  map-All P Q f pres [] = []
  map-All P Q f pres (px ∷ pxs) = pres px ∷ map-All P Q f pres pxs

  map-All₂ : ∀ {a b c d p q} 
             {A : Set a} {B : Set b} {C : Set c} {D : Set d} 
             (P : A → B → Set p) (Q : C → D → Set q) 
             (f : A → C) (g : B → D) → 
             (∀ {x y} → P x y → Q (f x) (g y)) →
             ∀ {n} {xs : Vec A n} {ys : Vec B n} → 
             All₂ P xs ys → All₂ Q (map f xs) (map g ys)
  map-All₂ P Q f g pres []            = []
  map-All₂ P Q f g pres (pxy ∷ pxsys) = pres pxy ∷ map-All₂ P Q f g pres pxsys

  foldr₂-All₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
             {_⊕ᵃ_ : Op₂ A} {_⊕ᵇ_ : Op₂ B} → 
             (∀ {w x y z} → P w x → P y z → P (w ⊕ᵃ y) (x ⊕ᵇ z)) →
             ∀ {n} {xs : Vec A n} {ys : Vec B n} {e₁} {e₂} → 
             P e₁ e₂ → All₂ P xs ys → P (foldr₂ _⊕ᵃ_ e₁ xs) (foldr₂ _⊕ᵇ_ e₂ ys)
  foldr₂-All₂ P pres pe₁e₂ []            = pe₁e₂
  foldr₂-All₂ P pres pe₁e₂ (pxy ∷ pxsys) = pres pxy (foldr₂-All₂ P pres pe₁e₂ pxsys)

  tabulate-All₂ : ∀ {a b p} {A : Set a} {B : Set b}
                  (P : A → B → Set p) {n} {f : Fin n → A} {g : Fin n → B}
                  → (∀ i → P (f i) (g i))
                  → All₂ P (tabulate f) (tabulate g)
  tabulate-All₂ P {zero} Pfg = []
  tabulate-All₂ P {suc n} Pfg = Pfg fzero ∷ tabulate-All₂ P (Pfg ∘ fsuc)
