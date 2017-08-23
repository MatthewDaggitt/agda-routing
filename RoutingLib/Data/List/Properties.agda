open import Data.Nat using (zero; suc; z≤n; s≤s; _≤_; _<_; _⊔_; _+_)
open import Data.Nat.Properties using (≤-step; ≤-antisym; ⊓-sel; ⊔-sel; m≤m⊔n; ⊔-mono-≤; +-suc; ⊔-identityʳ; n≤m⊔n; ⊓-mono-≤; ≤-refl; ≤-trans; <-transʳ; <-transˡ; m⊓n≤n; <⇒≢)
open import Data.List
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_; lose)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Unary using (Decidable; Pred; ∁)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)
open import Function using (id; _∘_)
open import Algebra.FunctionProperties using (Op₂; Idempotent; Associative; Commutative; Congruent₂)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.All using (All₂; []; _∷_)
open import RoutingLib.Data.List.All.Properties using (All-applyBetween⁺₁)
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Relation.Unary.Consequences using (P?⇒¬P?)
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.Properties where

  -- Properties of dfilter

  module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

    -- stdlib
    dfilter[xs]≡xs : ∀ {xs} → All P xs → dfilter P? xs ≡ xs
    dfilter[xs]≡xs {[]}     [] = refl
    dfilter[xs]≡xs {x ∷ xs} (px ∷ pxs) with P? x
    ... | no  ¬px = contradiction px ¬px
    ... | yes _   = cong (x ∷_) (dfilter[xs]≡xs pxs)

    -- stdlib
    dfilter[xs]≡[] : ∀ {xs} → All (∁ P) xs → dfilter P? xs ≡ []
    dfilter[xs]≡[] {[]} [] = refl
    dfilter[xs]≡[] {x ∷ xs} (¬px ∷ ¬pxs) with P? x
    ... | no  _  = dfilter[xs]≡[] ¬pxs
    ... | yes px = contradiction px ¬px

    -- stdlib
    |dfilter[xs]|≤|xs| : ∀ xs → length (dfilter P? xs) ≤ length xs
    |dfilter[xs]|≤|xs| [] = z≤n
    |dfilter[xs]|≤|xs| (x ∷ xs) with P? x
    ... | no  _ = ≤-step (|dfilter[xs]|≤|xs| xs)
    ... | yes _ = s≤s (|dfilter[xs]|≤|xs| xs)

    dfilter-length₂ : ∀ xs → length (dfilter (P?⇒¬P? P?) xs) + length (dfilter P? xs) ≡ length xs
    dfilter-length₂ [] = refl
    dfilter-length₂ (x ∷ xs) with P? x
    ... | no  _ = cong suc (dfilter-length₂ xs)
    ... | yes _ = trans (+-suc (length (dfilter (P?⇒¬P? P?) xs)) (length (dfilter P? xs))) (cong suc (dfilter-length₂ xs))


  -- Properties of gfilter

  module _ {a b} {A : Set a} {B : Set b} (P : A → Maybe B) where
  
    gfilter≡[] : ∀ {xs} → All (λ x → P x ≡ nothing) xs → gfilter P xs ≡ []
    gfilter≡[] {_}     [] = refl
    gfilter≡[] {x ∷ _} (Px≡nothing ∷ Pxs) with P x
    ... | nothing = gfilter≡[] Pxs
    ... | just _  = contradiction Px≡nothing λ()

    gfilter-cong : ∀ {xs ys} → All₂ (λ x y → P x ≡ P y) xs ys → gfilter P xs ≡ gfilter P ys
    gfilter-cong [] = refl
    gfilter-cong {x ∷ _} {y ∷ _} (Px≡Py ∷ Pxsys) with P x | P y
    ... | nothing | nothing = gfilter-cong Pxsys
    ... | nothing | just _  = contradiction Px≡Py λ()
    ... | just _  | nothing = contradiction Px≡Py λ()
    ... | just _  | just _  = cong₂ _∷_ (just-injective Px≡Py) (gfilter-cong Pxsys)


  -- Properties of tabulate

  module _ {a} {A : Set a} where
  
    tabulate-cong : ∀ {n ℓ} {_≈_ : Rel A ℓ} (f g : Fin n → A) → (∀ i → f i ≈ g i) → ListRel _≈_ (tabulate f) (tabulate g)
    tabulate-cong {zero}  f g f≈g = []
    tabulate-cong {suc n} f g f≈g = f≈g fzero ∷ tabulate-cong (f ∘ fsuc) (g ∘ fsuc) (f≈g ∘ fsuc)


  -- Properties of foldr

  module _ {a p} {A : Set a} {P : Pred A p} {_•_ : Op₂ A} where
  
    foldr-forces× : _•_ Forces-× P → ∀ e xs → P (foldr _•_ e xs) → All P xs
    foldr-forces× _          _ []       _     = []
    foldr-forces× •-forces-P _ (x ∷ xs) Pfold with •-forces-P _ _ Pfold
    ... | (px , pfxs) = px ∷ foldr-forces× •-forces-P _ xs pfxs

    foldr-×pres : _•_ ×-Preserves P → ∀ {e xs} → All P xs → P e → P (foldr _•_ e xs)
    foldr-×pres _    []         pe = pe
    foldr-×pres pres (px ∷ pxs) pe = pres px (foldr-×pres pres pxs pe)
  
    foldr-⊎presʳ : _•_ ⊎-Preservesʳ P → ∀ {e} xs → P e → P (foldr _•_ e xs)
    foldr-⊎presʳ •-pres-P []       Pe = Pe
    foldr-⊎presʳ •-pres-P (_ ∷ xs) Pe = •-pres-P _ (foldr-⊎presʳ •-pres-P xs Pe)

    foldr-⊎pres : _•_ ⊎-Preserves P → ∀ {xs} e → Any P xs → P (foldr _•_ e xs)
    foldr-⊎pres •-pres-P e (here px)   = •-pres-P _ _ (inj₁ px)
    foldr-⊎pres •-pres-P e (there pxs) = •-pres-P _ _ (inj₂ (foldr-⊎pres •-pres-P e pxs))

  -- Properties of zipWith
  
  zipWith-comm : ∀ {a b} {A : Set a} {B : Set b} {f : A → A → B} → (∀ x y → f x y ≡ f y x) → ∀ xs ys → zipWith f xs ys ≡ zipWith f ys xs
  zipWith-comm f-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (f-comm x y) (zipWith-comm f-comm xs ys)
  zipWith-comm f-comm []       []       = refl
  zipWith-comm f-comm []       (x ∷ ys) = refl
  zipWith-comm f-comm (x ∷ xs) []       = refl
  
  -- Properties of index
  
  index∈xs : ∀ {a} {A : Set a} (xs : List A) {i} (i<|xs| : i < length xs) → index xs i<|xs| ∈ xs
  index∈xs []       {_}     ()
  index∈xs (x ∷ xs) {zero}  (s≤s i<|xs|) = here refl
  index∈xs (x ∷ xs) {suc i} (s≤s i<|xs|) = there (index∈xs xs i<|xs|)



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
    
    foldr≤ᵣe : ∀ {_•_ : Op₂ A} → Congruent₂ _≈_ _•_ → Idempotent _≈_ _•_ → Associative _≈_ _•_ → Commutative _≈_ _•_ → ∀ e xs → e • foldr _•_ e xs ≈ foldr _•_ e xs
    foldr≤ᵣe {_}   •-cong •-idem •-assoc •-comm e [] = •-idem e
    foldr≤ᵣe {_•_} •-cong •-idem •-assoc •-comm e (x ∷ xs) = 
      begin
        e • (x • foldr _•_ e xs) ≈⟨ ≈-sym (•-assoc e x _) ⟩
        (e • x) • foldr _•_ e xs ≈⟨ •-cong (•-comm e x) ≈-refl ⟩
        (x • e) • foldr _•_ e xs ≈⟨ •-assoc x e _ ⟩
        x • (e • foldr _•_ e xs) ≈⟨ •-cong ≈-refl (foldr≤ᵣe •-cong •-idem •-assoc •-comm e xs) ⟩
        x • foldr _•_ e xs
      ∎

    foldr≤ₗe : ∀ {_•_ : Op₂ A} → Congruent₂ _≈_ _•_ → Idempotent _≈_ _•_ → Associative _≈_ _•_ → Commutative _≈_ _•_ → ∀ e xs → foldr _•_ e xs • e ≈ foldr _•_ e xs
    foldr≤ₗe •-cong •-idem •-assoc •-comm e xs = ≈-trans (•-comm _ e) (foldr≤ᵣe •-cong •-idem •-assoc •-comm e xs)
      

    foldr≤ᵣxs : ∀ {_•_ : Op₂ A} → Congruent₂ _≈_ _•_ → Idempotent _≈_ _•_ → Associative _≈_ _•_ → Commutative _≈_ _•_ → ∀ e {x xs} → x ∈ₛ xs → x • foldr _•_ e xs ≈ foldr _•_ e xs
    foldr≤ᵣxs {_•_} •-cong •-idem •-assoc •-comm e {x} {y ∷ xs} (here x≈y) =
      begin
        x • (y • foldr _•_ e xs) ≈⟨ ≈-sym (•-assoc x y _) ⟩
        (x • y) • foldr _•_ e xs ≈⟨ •-cong (•-cong x≈y ≈-refl) ≈-refl ⟩
        (y • y) • foldr _•_ e xs ≈⟨ •-cong (•-idem y) ≈-refl ⟩
        y • foldr _•_ e xs
      ∎
    foldr≤ᵣxs {_•_} •-cong •-idem •-assoc •-comm e {x} {y ∷ xs} (there x∈xs) =
      begin
        x • (y • foldr _•_ e xs) ≈⟨ ≈-sym (•-assoc x y _) ⟩
        (x • y) • foldr _•_ e xs ≈⟨ •-cong (•-comm x y) ≈-refl ⟩
        (y • x) • foldr _•_ e xs ≈⟨ •-assoc y x _ ⟩
        y • (x • foldr _•_ e xs) ≈⟨ •-cong ≈-refl (foldr≤ᵣxs •-cong •-idem •-assoc •-comm e x∈xs) ⟩
        y • foldr _•_ e xs
      ∎

    foldr≤ₗxs : ∀ {_•_ : Op₂ A} → Congruent₂ _≈_ _•_ → Idempotent _≈_ _•_ → Associative _≈_ _•_ → Commutative _≈_ _•_ → ∀ e {x xs} → x ∈ₛ xs → foldr _•_ e xs • x ≈ foldr _•_ e xs
    foldr≤ₗxs •-cong •-idem •-assoc •-comm e x∈xs = ≈-trans (•-comm _ _) (foldr≤ᵣxs •-cong •-idem •-assoc •-comm e x∈xs)

    foldr-map-commute : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} → Congruent₂ _≈_ _•ᵃ_ → (∀ x y → f x •ᵃ f y ≈ f (x •ᵇ y)) → ∀ {e d} → e ≈ f d → ∀ xs → foldr _•ᵃ_ e (map f xs) ≈  f (foldr _•ᵇ_ d xs)
    foldr-map-commute _       _      e≈fd []       = e≈fd
    foldr-map-commute •ᵃ-cong f-cong e≈fd (x ∷ xs) = ≈-trans (•ᵃ-cong ≈-refl (foldr-map-commute •ᵃ-cong f-cong e≈fd xs)) (f-cong x _)

