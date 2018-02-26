open import Data.Nat using (zero; suc; z≤n; s≤s; _≤_; _<_; _⊔_; _+_)
open import Data.Nat.Properties using (≤-step; ≤-antisym; ⊓-sel; ⊔-sel; m≤m⊔n; ⊔-mono-≤; +-suc; ⊔-identityʳ; n≤m⊔n; ⊓-mono-≤; ≤-refl; ≤-trans; <-transʳ; <-transˡ; m⊓n≤n; <⇒≢; ≤+≢⇒<; suc-injective)
open import Data.List
open import Data.List.Properties using (length-filter)
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_; lose)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing; just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Unary using (Decidable; Pred; ∁; ∁?)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Algebra.FunctionProperties using (Op₂; Idempotent; Associative; Commutative; Congruent₂)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.All using ([]; _∷_)
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.Properties where

  -- Properties of dfilter

  module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

    |filter[xs]|<|xs| : ∀ xs → Any (λ x → ¬ (P x)) xs → length (filter P? xs) < length xs
    |filter[xs]|<|xs| [] ()
    |filter[xs]|<|xs| (x ∷ xs) (here ¬px) with P? x
    ... | no  _  = s≤s (length-filter P? xs) --(|filter[xs]|≤|xs| xs)
    ... | yes px = contradiction px ¬px
    |filter[xs]|<|xs| (x ∷ xs) (there any) with P? x
    ... | no  _ = ≤-step (|filter[xs]|<|xs| xs any)
    ... | yes _ = s≤s (|filter[xs]|<|xs| xs any)

    |filter[xs]|≡|xs|⇒filter[xs]≡xs : ∀ {xs} → length (filter P? xs) ≡ length xs →
                                          filter P? xs ≡ xs
    |filter[xs]|≡|xs|⇒filter[xs]≡xs {[]} length≡ = refl
    |filter[xs]|≡|xs|⇒filter[xs]≡xs {x ∷ xs} length≡ with P? x
    ... | no ¬px = contradiction length≡ (<⇒≢ (s≤s (length-filter P? xs)))
    ... | yes px = cong (x ∷_) (|filter[xs]|≡|xs|⇒filter[xs]≡xs {xs} (suc-injective length≡))

    filter-length₂ : ∀ xs → length (filter (∁? P?) xs) + length (filter P? xs) ≡ length xs
    filter-length₂ [] = refl
    filter-length₂ (x ∷ xs) with P? x
    ... | no  _ = cong suc (filter-length₂ xs)
    ... | yes _ = trans (+-suc (length (filter (∁? P?) xs)) (length (filter P? xs))) (cong suc (filter-length₂ xs))

  -- Properties of gfilter

  module _ {a b} {A : Set a} {B : Set b} (P : A → Maybe B) where
  
    mapMaybe≡[] : ∀ {xs} → All (λ x → P x ≡ nothing) xs → mapMaybe P xs ≡ []
    mapMaybe≡[] {_}     [] = refl
    mapMaybe≡[] {x ∷ _} (Px≡nothing ∷ Pxs) with P x
    ... | nothing = mapMaybe≡[] Pxs
    ... | just _  = contradiction Px≡nothing λ()

    mapMaybe-cong : ∀ {xs ys} → Pointwise (λ x y → P x ≡ P y) xs ys →
                    mapMaybe P xs ≡ mapMaybe P ys
    mapMaybe-cong [] = refl
    mapMaybe-cong {x ∷ _} {y ∷ _} (Px≡Py ∷ Pxsys) with P x | P y
    ... | nothing | nothing = mapMaybe-cong Pxsys
    ... | nothing | just _  = contradiction Px≡Py λ()
    ... | just _  | nothing = contradiction Px≡Py λ()
    ... | just _  | just _  = cong₂ _∷_ (just-injective Px≡Py) (mapMaybe-cong Pxsys)


  -- Properties of tabulate

  module _ {a} {A : Set a} where
  
    tabulate-cong : ∀ {n ℓ} {_≈_ : Rel A ℓ} (f g : Fin n → A) → (∀ i → f i ≈ g i) → ListRel _≈_ (tabulate f) (tabulate g)
    tabulate-cong {zero}  f g f≈g = []
    tabulate-cong {suc n} f g f≈g = f≈g fzero ∷ tabulate-cong (f ∘ fsuc) (g ∘ fsuc) (f≈g ∘ fsuc)


  -- Properties of foldr

  module _ {a p} {A : Set a} {P : Pred A p} {_•_ : Op₂ A} where
  
    foldr-forces× : _•_ Forces-× P → ∀ e xs → P (foldr _•_ e xs) → All P xs
    foldr-forces× _          _ []       _     = []
    foldr-forces× forces _ (x ∷ xs) Pfold with forces _ _ Pfold
    ... | (px , pfxs) = px ∷ foldr-forces× forces _ xs pfxs

    foldr-×pres : _•_ ×-Preserves P → ∀ {e xs} → All P xs → P e → P (foldr _•_ e xs)
    foldr-×pres _    []         pe = pe
    foldr-×pres pres (px ∷ pxs) pe = pres px (foldr-×pres pres pxs pe)

    foldr-⊎presʳ : _•_ ⊎-Preservesʳ P → ∀ {e} xs → P e → P (foldr _•_ e xs)
    foldr-⊎presʳ pres []       Pe = Pe
    foldr-⊎presʳ pres (_ ∷ xs) Pe = pres _ (foldr-⊎presʳ pres xs Pe)

    foldr-⊎pres : _•_ ⊎-Preserves P → ∀ {xs} e → Any P xs → P (foldr _•_ e xs)
    foldr-⊎pres pres e (here px)   = pres _ _ (inj₁ px)
    foldr-⊎pres pres e (there pxs) = pres _ _ (inj₂ (foldr-⊎pres pres e pxs))


  -- Properties of foldl

  module _ {a p} {A : Set a} {P : Pred A p} {_•_ : Op₂ A} where

{-
    foldl-forces× : _•_ Forces-× P → ∀ e xs → P (foldl _•_ e xs) → All P xs
    foldl-forces× _      _ []       _     = []
    foldl-forces× forces e (x ∷ xs) Pfold with forces {!!} {!!} {!!}
    ... | (px , pfxs) = {!!} --px ∷ foldl-forces× •-forces-P _ xs pfxs
-}

    foldl-×pres : _•_ ×-Preserves P → ∀ {e xs} → All P xs → P e → P (foldl _•_ e xs)
    foldl-×pres _    []         pe = pe
    foldl-×pres pres (px ∷ pxs) pe = foldl-×pres pres pxs (pres pe px)
    
    foldl-⊎presˡ : _•_ ⊎-Preservesˡ P → ∀ {e} xs → P e → P (foldl _•_ e xs)
    foldl-⊎presˡ pres []       Pe = Pe
    foldl-⊎presˡ pres (x ∷ xs) Pe = foldl-⊎presˡ pres xs (pres x Pe)
    
    foldl-⊎pres : _•_ ⊎-Preserves P → ∀ {xs} e → Any P xs → P (foldl _•_ e xs)
    foldl-⊎pres pres {x ∷ xs} e (here px)   = foldl-⊎presˡ (⊎pres⇒⊎presˡ pres) xs (pres e _ (inj₂ px))
    foldl-⊎pres pres {x ∷ xs} e (there pxs) = foldl-⊎pres pres _ pxs
    
  -- Properties of zipWith
  
  zipWith-comm : ∀ {a b} {A : Set a} {B : Set b} {f : A → A → B} → (∀ x y → f x y ≡ f y x) → ∀ xs ys → zipWith f xs ys ≡ zipWith f ys xs
  zipWith-comm f-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (f-comm x y) (zipWith-comm f-comm xs ys)
  zipWith-comm f-comm []       []       = refl
  zipWith-comm f-comm []       (x ∷ ys) = refl
  zipWith-comm f-comm (x ∷ xs) []       = refl
  
  -- Properties of index
  
  lookup∈xs : ∀ {a} {A : Set a} (xs : List A) (i : Fin (length xs)) → lookup xs i ∈ xs
  lookup∈xs []       ()     
  lookup∈xs (x ∷ xs) fzero    = here refl
  lookup∈xs (x ∷ xs) (fsuc i) = there (lookup∈xs xs i)

  -- Properties of min

  min[xs]≤x : ∀ {x xs} ⊤ → Any (_≤ x) xs → min ⊤ xs ≤ x
  min[xs]≤x = foldr-⊎pres n≤m⊎o≤m⇒n⊓o≤m

  min[xs]<x : ∀ {x xs} ⊤ → Any (_< x) xs → min ⊤ xs < x
  min[xs]<x = foldr-⊎pres n<m⊎o<m⇒n⊓o<m
  
  min[xs]≤⊤ : ∀ ⊤ xs → min ⊤ xs ≤ ⊤
  min[xs]≤⊤ ⊤ xs = foldr-⊎presʳ o≤m⇒n⊓o≤m xs ≤-refl

  x≤min[xs] : ∀ {x xs ⊤} → All (x ≤_) xs → x ≤ ⊤ → x ≤ min ⊤ xs
  x≤min[xs] = foldr-×pres m≤n×m≤o⇒m≤n⊓o

  x<min[xs] : ∀ {x xs ⊤} → All (x <_) xs → x < ⊤ → x < min ⊤ xs
  x<min[xs] = foldr-×pres m≤n×m≤o⇒m≤n⊓o

  min[xs]≡x : ∀ {x xs ⊤} → x ∈ xs → All (x ≤_) xs → x ≤ ⊤ → min ⊤ xs ≡ x
  min[xs]≡x x∈xs x≤xs x≤⊤ = ≤-antisym (min[xs]≤x _ (lose x∈xs ≤-refl)) (x≤min[xs] x≤xs x≤⊤)
  
  min[xs]∈xs : ∀ {⊤ xs} → min ⊤ xs ≢ ⊤ → min ⊤ xs ∈ xs
  min[xs]∈xs {⊤} {[]}     ⊤≢⊤ = contradiction refl ⊤≢⊤
  min[xs]∈xs {⊤} {x ∷ xs} m≢⊤ with ⊓-sel x (min ⊤ xs)
  ... | inj₁ y⊓m≡y rewrite y⊓m≡y = here refl
  ... | inj₂ y⊓m≡m rewrite y⊓m≡m = there (min[xs]∈xs m≢⊤)
  
  min[xs]<min[ys]₁ : ∀ {xs ys ⊤₁ ⊤₂} → ⊤₁ < ⊤₂ → All (λ y → Any (_< y) xs) ys → min ⊤₁ xs < min ⊤₂ ys
  min[xs]<min[ys]₁ {xs} {[]}     {_}  {_}  ⊤₁<⊤₂ [] = <-transʳ (min[xs]≤⊤ _ xs) ⊤₁<⊤₂
  min[xs]<min[ys]₁ {xs} {y ∷ ys} {⊤₁} {⊤₂} ⊤₁<⊤₂ (xs<y  ∷ pxs) with ⊓-sel y (min ⊤₂ ys)
  ... | inj₁ y⊓m≡y rewrite y⊓m≡y = min[xs]<x ⊤₁ xs<y
  ... | inj₂ y⊓m≡m rewrite y⊓m≡m = min[xs]<min[ys]₁ ⊤₁<⊤₂ pxs

  min[xs]<min[ys]₃ : ∀ {xs ys} ⊤₁ {⊤₂} → Any (_< ⊤₂) xs → All (λ y → Any (_< y) xs) ys → min ⊤₁ xs < min ⊤₂ ys
  min[xs]<min[ys]₃ {_} {[]}     ⊤₁ {⊤₂} xs<⊤₂ [] = min[xs]<x ⊤₁ xs<⊤₂
  min[xs]<min[ys]₃ {_} {y ∷ ys} ⊤₁ {⊤₂} xs<⊤₂ (xs<y ∷ pys) with ⊓-sel y (min ⊤₂ ys)
  ... | inj₁ y⊓m≡y rewrite y⊓m≡y = min[xs]<x ⊤₁ xs<y
  ... | inj₂ y⊓m≡m rewrite y⊓m≡m = min[xs]<min[ys]₃ ⊤₁ xs<⊤₂ pys



  -- Properties of max

  max[xs]≤x : ∀ {x xs ⊥} → All (_≤ x) xs → ⊥ ≤ x → max ⊥ xs ≤ x
  max[xs]≤x = foldr-×pres n≤m×o≤m⇒n⊔o≤m

  max[xs]<x : ∀ {x xs ⊥} → All (_< x) xs → ⊥ < x → max ⊥ xs < x
  max[xs]<x = foldr-×pres n≤m×o≤m⇒n⊔o≤m

  x≤max[xs] : ∀ {x xs} ⊥ → Any (x ≤_) xs → x ≤ max ⊥ xs
  x≤max[xs] = foldr-⊎pres m≤n⊎m≤o⇒m≤n⊔o
  
  x<max[xs] : ∀ {x xs} ⊥ → Any (x <_) xs → x < max ⊥ xs
  x<max[xs] = foldr-⊎pres m≤n⊎m≤o⇒m≤n⊔o

  ⊥≤max[xs] : ∀ ⊥ xs → ⊥ ≤ max ⊥ xs
  ⊥≤max[xs] ⊥ xs = foldr-⊎presʳ m≤o⇒m≤n⊔o xs ≤-refl
  
  max[xs]≡x : ∀ {x xs ⊥} → x ∈ xs → All (_≤ x) xs → ⊥ ≤ x → max ⊥ xs ≡ x
  max[xs]≡x x∈xs xs≤x ⊥≤x = ≤-antisym (max[xs]≤x xs≤x ⊥≤x) (x≤max[xs] _ (lose x∈xs ≤-refl))
  
  max[xs]∈xs : ∀ {⊥ xs} → max ⊥ xs ≢ ⊥ → max ⊥ xs ∈ xs
  max[xs]∈xs {⊥} {[]}     ⊥≢⊥ = contradiction refl ⊥≢⊥
  max[xs]∈xs {⊥} {x ∷ xs} m≢⊥ with ⊔-sel x (max ⊥ xs)
  ... | inj₁ x⊔r≡x rewrite x⊔r≡x = here refl
  ... | inj₂ x⊔r≡r rewrite x⊔r≡r = there (max[xs]∈xs m≢⊥)



  module _ {a ℓ} (S : Setoid a ℓ) where

    open Setoid S renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
    open import Data.List.Any.Membership S using () renaming (_∈_ to _∈ₛ_)
    open import Relation.Binary.EqReasoning S

    module _ {_•_ : Op₂ A}
             (•-cong : Congruent₂ _≈_ _•_) (•-idem : Idempotent _≈_ _•_)
             (•-assoc : Associative _≈_ _•_) (•-comm : Commutative _≈_ _•_)
             where
             
      foldr≤ᵣe : ∀ e xs → e • foldr _•_ e xs ≈ foldr _•_ e xs
      foldr≤ᵣe e [] = •-idem e
      foldr≤ᵣe e (x ∷ xs) = 
        begin
          e • (x • foldr _•_ e xs) ≈⟨ ≈-sym (•-assoc e x _) ⟩
          (e • x) • foldr _•_ e xs ≈⟨ •-cong (•-comm e x) ≈-refl ⟩
          (x • e) • foldr _•_ e xs ≈⟨ •-assoc x e _ ⟩
          x • (e • foldr _•_ e xs) ≈⟨ •-cong ≈-refl (foldr≤ᵣe e xs) ⟩
          x • foldr _•_ e xs
        ∎

      foldr≤ₗe : ∀ e xs → foldr _•_ e xs • e ≈ foldr _•_ e xs
      foldr≤ₗe e xs = ≈-trans (•-comm _ e) (foldr≤ᵣe e xs)
      

      foldr≤ᵣxs : ∀ e {x xs} → x ∈ₛ xs → x • foldr _•_ e xs ≈ foldr _•_ e xs
      foldr≤ᵣxs e {x} {y ∷ xs} (here x≈y) =
        begin
          x • (y • foldr _•_ e xs) ≈⟨ ≈-sym (•-assoc x y _) ⟩
          (x • y) • foldr _•_ e xs ≈⟨ •-cong (•-cong x≈y ≈-refl) ≈-refl ⟩
          (y • y) • foldr _•_ e xs ≈⟨ •-cong (•-idem y) ≈-refl ⟩
          y • foldr _•_ e xs
        ∎
      foldr≤ᵣxs e {x} {y ∷ xs} (there x∈xs) =
        begin
          x • (y • foldr _•_ e xs) ≈⟨ ≈-sym (•-assoc x y _) ⟩
          (x • y) • foldr _•_ e xs ≈⟨ •-cong (•-comm x y) ≈-refl ⟩
          (y • x) • foldr _•_ e xs ≈⟨ •-assoc y x _ ⟩
          y • (x • foldr _•_ e xs) ≈⟨ •-cong ≈-refl (foldr≤ᵣxs e x∈xs) ⟩
          y • foldr _•_ e xs
        ∎

      foldr≤ₗxs : ∀ e {x xs} → x ∈ₛ xs → foldr _•_ e xs • x ≈ foldr _•_ e xs
      foldr≤ₗxs e x∈xs = ≈-trans (•-comm _ _) (foldr≤ᵣxs e x∈xs)

    foldr-map-commute : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} → Congruent₂ _≈_ _•ᵃ_ → (∀ x y → f x •ᵃ f y ≈ f (x •ᵇ y)) → ∀ {e d} → e ≈ f d → ∀ xs → foldr _•ᵃ_ e (map f xs) ≈  f (foldr _•ᵇ_ d xs)
    foldr-map-commute _       _      e≈fd []       = e≈fd
    foldr-map-commute •ᵃ-cong f-cong e≈fd (x ∷ xs) = ≈-trans (•ᵃ-cong ≈-refl (foldr-map-commute •ᵃ-cong f-cong e≈fd xs)) (f-cong x _)
