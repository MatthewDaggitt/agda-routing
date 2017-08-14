open import Data.Vec as Vec hiding (map; zip)
open import Data.Vec.All using (All; []; _∷_) renaming (map to mapₐ; lookup to lookupₐ)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Fin using (Fin; _<_) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (zero; suc; s≤s)
open import Data.List using ([]; _∷_)
open import Data.List.All using ([]; _∷_) renaming (All to Allₗ)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)
open import Relation.Binary using (Rel; _⇒_)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.Vec using (map; zip; foldr₂)
open import RoutingLib.Data.Vec.All using (All₂; AllPairs; []; _∷_)
open import RoutingLib.Data.List.All using ([]; _∷_) renaming (AllPairs to AllPairsₗ)

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



  AllPairs-lookup : ∀ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} {n} {xs : Vec A n} → AllPairs _~_ xs → ∀ {i j} → i < j → lookup i xs ~ lookup j xs
  AllPairs-lookup [] {()}
  AllPairs-lookup (x~xs ∷ pxs) {_}      {fzero}  ()
  AllPairs-lookup (x~xs ∷ pxs) {fzero}  {fsuc j} (s≤s i<j) = lookupₐ j x~xs
  AllPairs-lookup (x~xs ∷ pxs) {fsuc i} {fsuc j} (s≤s i<j) = AllPairs-lookup pxs i<j



  -- All & fromList
  
  module _ {a p} {A : Set a} {P : A → Set p} where
  
    All-fromList⁺ : ∀ {xs} → Allₗ P xs → All P (fromList xs)
    All-fromList⁺ []         = []
    All-fromList⁺ (px ∷ pxs) = px ∷ All-fromList⁺ pxs

    All-fromList⁻ : ∀ {xs} → All P (fromList xs) → Allₗ P xs
    All-fromList⁻ {[]}     []         = []
    All-fromList⁻ {x ∷ xs} (px ∷ pxs) = px ∷ (All-fromList⁻ pxs)

  -- AllPairs & fromList
  
  module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

    AllPairs-fromList⁺ : ∀ {xs} → AllPairsₗ _~_ xs → AllPairs _~_ (fromList xs)
    AllPairs-fromList⁺ [] = []
    AllPairs-fromList⁺ (px ∷ pxs) = (All-fromList⁺ px) ∷ (AllPairs-fromList⁺ pxs)



  -- All & toList
  
  module _ {a p} {A : Set a} {P : A → Set p} where

    All-toList⁺ : ∀ {n} {xs : Vec A n} → Allₗ P (toList xs) → All P xs
    All-toList⁺ {xs = []}     []         = []
    All-toList⁺ {xs = x ∷ xs} (px ∷ pxs) = px ∷ All-toList⁺ pxs
    
    All-toList⁻ : ∀ {n} {xs : Vec A n} → All P xs → Allₗ P (toList xs)
    All-toList⁻ [] = []
    All-toList⁻ (px ∷ pxs) = px ∷ All-toList⁻ pxs
