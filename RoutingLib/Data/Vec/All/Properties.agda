open import Data.Vec hiding (map; zip)
open import Data.Vec.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.Product using (_×_; _,_; uncurry)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)
open import Relation.Binary using (_⇒_)
open import Function using (_∘_)

open import RoutingLib.Data.Vec using (map; zip)
open import RoutingLib.Data.Vec.All using (All₂)

module RoutingLib.Data.Vec.All.Properties where

  map-All : ∀ {a b p q} {A : Set a} {B : Set b} 
            (P : A → Set p) (Q : B → Set q) (f : A → B) → 
            P ⋐ Q ∘ f → 
            ∀ {n} {xs : Vec A n} → All P xs → All Q (map f xs)
  map-All P Q f pres [] = []
  map-All P Q f pres (px ∷ pxs) = pres px ∷ map-All P Q f pres pxs

{-
  map-All₂ : ∀ {a b c d p q} 
             {A : Set a} {B : Set b} {C : Set c} {D : Set d} 
             (P : A → B → Set p) (Q : C → D → Set q) 
             (f : A → C) (g : B → D) → 
             (∀ {x y} → P x y → Q (f x) (g y)) →
             ∀ {n} {xs : Vec A n} {ys : Vec B n} → 
             All₂ P xs ys → All₂ Q (map f xs) (map g ys)
  map-All₂ {A = A} {B} {C} {D} P Q f g pres {xs = xs} {ys} pxsys = map-All {A = A × B} {B = C × D} (uncurry P) (uncurry Q) (λ {(a , b) → (f a , g b)}) pres {xs = {!!}} {!pxsys!}
-}
