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
open import Relation.Unary using (∁)
open import Function using (id; _∘_)
open import Algebra.FunctionProperties using (Op₂; Idempotent; Associative; Commutative; Congruent₂)

open import RoutingLib.Algebra using (Semilattice)
open import RoutingLib.Data.List
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.Properties where

------------------------------------------------------------------------
-- Properties of filter

module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

  filter-length₂ : ∀ xs → length (filter (∁? P?) xs) + length (filter P? xs) ≡ length xs
  filter-length₂ [] = refl
  filter-length₂ (x ∷ xs) with P? x
  ... | no  _ = cong suc (filter-length₂ xs)
  ... | yes _ = trans (+-suc (length (filter (∁? P?) xs)) (length (filter P? xs))) (cong suc (filter-length₂ xs))

------------------------------------------------------------------------
-- Properties of mapMaybe

module _ {a b} {A : Set a} {B : Set b} (f : A → Maybe B) where

  mapMaybe≡[] : ∀ {xs} → All (λ x → f x ≡ nothing) xs → mapMaybe f xs ≡ []
  mapMaybe≡[] {_}     [] = refl
  mapMaybe≡[] {x ∷ _} (fx≡nothing ∷ fxs) with f x
  ... | nothing = mapMaybe≡[] fxs
  ... | just _  = contradiction fx≡nothing λ()

  mapMaybe-cong : ∀ {xs ys} → Pointwise (λ x y → f x ≡ f y) xs ys →
                  mapMaybe f xs ≡ mapMaybe f ys
  mapMaybe-cong [] = refl
  mapMaybe-cong {x ∷ _} {y ∷ _} (fx≡fy ∷ fxsys) with f x | f y
  ... | nothing | nothing = mapMaybe-cong fxsys
  ... | nothing | just _  = contradiction fx≡fy λ()
  ... | just _  | nothing = contradiction fx≡fy λ()
  ... | just _  | just _  = cong₂ _∷_ (just-injective fx≡fy) (mapMaybe-cong fxsys)

------------------------------------------------------------------------
-- Properties of tabulate

module _ {a} {A : Set a} where

  -- stdlib
  tabulate-cong : ∀ {n ℓ} {_≈_ : Rel A ℓ} (f g : Fin n → A) →
                  (∀ i → f i ≈ g i) → ListRel _≈_ (tabulate f) (tabulate g)
  tabulate-cong {zero}  f g f≈g = []
  tabulate-cong {suc n} f g f≈g = f≈g fzero ∷ tabulate-cong (f ∘ fsuc) (g ∘ fsuc) (f≈g ∘ fsuc)


------------------------------------------------------------------------
-- Properties of foldr

module _ {a p} {A : Set a} {P : Pred A p} {_•_ : Op₂ A} where

  foldr-forcesᵇ : _•_ Forcesᵇ P → ∀ e xs → P (foldr _•_ e xs) → All P xs
  foldr-forcesᵇ _          _ []       _     = []
  foldr-forcesᵇ forces _ (x ∷ xs) Pfold with forces _ _ Pfold
  ... | (px , pfxs) = px ∷ foldr-forcesᵇ forces _ xs pfxs

  foldr-presᵇ : _•_ Preservesᵇ P → ∀ {e xs} → P e → All P xs → P (foldr _•_ e xs)
  foldr-presᵇ _    pe []         = pe
  foldr-presᵇ pres pe (px ∷ pxs) = pres px (foldr-presᵇ pres pe pxs)

  foldr-presʳ : _•_ Preservesʳ P → ∀ {e} → P e → ∀ xs → P (foldr _•_ e xs)
  foldr-presʳ pres pe []       = pe
  foldr-presʳ pres pe (_ ∷ xs) = pres _ (foldr-presʳ pres pe xs)

  foldr-presᵒ : _•_ Preservesᵒ P → ∀ e xs → P e ⊎ Any P xs → P (foldr _•_ e xs)
  foldr-presᵒ pres e []       (inj₁ pe) = pe
  foldr-presᵒ pres e []       (inj₂ ())
  foldr-presᵒ pres e (x ∷ xs) (inj₁ pe) = pres _ _ (inj₂ (foldr-presᵒ pres e xs (inj₁ pe)))
  foldr-presᵒ pres e (x ∷ xs) (inj₂ (here px))   = pres _ _ (inj₁ px)
  foldr-presᵒ pres e (x ∷ xs) (inj₂ (there pxs)) = pres _ _ (inj₂ (foldr-presᵒ pres e xs (inj₂ pxs)))

------------------------------------------------------------------------
-- Properties of foldl

module _ {a p} {A : Set a} {P : Pred A p} {_•_ : Op₂ A} where

{-
  foldl-forces× : _•_ Forces-× P → ∀ e xs → P (foldl _•_ e xs) → All P xs
  foldl-forces× _      _ []       _     = []
  foldl-forces× forces e (x ∷ xs) Pfold with forces {!!} {!!} {!!}
  ... | (px , pfxs) = {!!} --px ∷ foldl-forces× •-forces-P _ xs pfxs
-}

  foldl-×pres : _•_ Preservesᵇ P → ∀ {e xs} → P e → All P xs → P (foldl _•_ e xs)
  foldl-×pres _    pe []         = pe
  foldl-×pres pres pe (px ∷ pxs) = foldl-×pres pres (pres pe px) pxs

  foldl-⊎presˡ : _•_ Preservesˡ P → ∀ {e} → P e → ∀ xs → P (foldl _•_ e xs)
  foldl-⊎presˡ pres pe []       = pe
  foldl-⊎presˡ pres pe (x ∷ xs) = foldl-⊎presˡ pres (pres x pe) xs

  foldl-⊎pres : _•_ Preservesᵒ P → ∀ {xs} e → Any P xs → P (foldl _•_ e xs)
  foldl-⊎pres pres {x ∷ xs} e (here px)   = foldl-⊎presˡ (presᵒ⇒presˡ pres) (pres e _ (inj₂ px)) xs
  foldl-⊎pres pres {x ∷ xs} e (there pxs) = foldl-⊎pres pres _ pxs

-- Properties of index

lookup∈xs : ∀ {a} {A : Set a} (xs : List A) (i : Fin (length xs)) →
            lookup xs i ∈ xs
lookup∈xs []       ()     
lookup∈xs (x ∷ xs) fzero    = here refl
lookup∈xs (x ∷ xs) (fsuc i) = there (lookup∈xs xs i)





module _ {a ℓ} (S : Semilattice a ℓ)  where

  open Semilattice S renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open import Data.List.Any.Membership setoid using () renaming (_∈_ to _∈ₛ_)
  open import Relation.Binary.EqReasoning setoid

  foldr≤ᵣe : ∀ e xs → e ∧ foldr _∧_ e xs ≈ foldr _∧_ e xs
  foldr≤ᵣe e [] = idem e
  foldr≤ᵣe e (x ∷ xs) = begin
    e ∧ (x ∧ foldr _∧_ e xs) ≈⟨ ≈-sym (assoc e x _) ⟩
    (e ∧ x) ∧ foldr _∧_ e xs ≈⟨ ∙-cong (comm e x) ≈-refl ⟩
    (x ∧ e) ∧ foldr _∧_ e xs ≈⟨ assoc x e _ ⟩
    x ∧ (e ∧ foldr _∧_ e xs) ≈⟨ ∙-cong ≈-refl (foldr≤ᵣe e xs) ⟩
    x ∧ foldr _∧_ e xs       ∎

  open import RoutingLib.Relation.Binary.NaturalOrder.Right _≈_ _∧_
    using (≤-isTotalOrder) renaming (_≤_ to _≤ᵣ_)

  foldr≤ₗe : ∀ e xs → foldr _∧_ e xs ∧ e ≈ foldr _∧_ e xs
  foldr≤ₗe e xs = ≈-trans (comm _ e) (foldr≤ᵣe e xs)

  foldr≤ᵣxs : ∀ e {x xs} → x ∈ₛ xs → foldr _∧_ e xs ≤ᵣ x
  foldr≤ᵣxs e {x} {y ∷ xs} (here x≈y) = begin
    x ∧ (y ∧ foldr _∧_ e xs) ≈⟨ ≈-sym (assoc x y _) ⟩
    (x ∧ y) ∧ foldr _∧_ e xs ≈⟨ ∙-cong (∙-cong x≈y ≈-refl) ≈-refl ⟩
    (y ∧ y) ∧ foldr _∧_ e xs ≈⟨ ∙-cong (idem y) ≈-refl ⟩
    y ∧ foldr _∧_ e xs       ∎
  foldr≤ᵣxs e {x} {y ∷ xs} (there x∈xs) = begin
    x ∧ (y ∧ foldr _∧_ e xs) ≈⟨ ≈-sym (assoc x y _) ⟩
    (x ∧ y) ∧ foldr _∧_ e xs ≈⟨ ∙-cong (comm x y) ≈-refl ⟩
    (y ∧ x) ∧ foldr _∧_ e xs ≈⟨ assoc y x _ ⟩
    y ∧ (x ∧ foldr _∧_ e xs) ≈⟨ ∙-cong ≈-refl (foldr≤ᵣxs e x∈xs) ⟩
    y ∧ foldr _∧_ e xs       ∎

  foldr≤ₗxs : ∀ e {x xs} → x ∈ₛ xs → foldr _∧_ e xs ∧ x ≈ foldr _∧_ e xs
  foldr≤ₗxs e x∈xs = ≈-trans (comm _ _) (foldr≤ᵣxs e x∈xs)




module _ {a ℓ} (S : Setoid a ℓ)  where

  open Setoid S renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open import Relation.Binary.EqReasoning S

  foldr-map-commute : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} →
                      Congruent₂ _≈_ _•ᵃ_ →
                      (∀ x y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                      ∀ {e d} → e ≈ f d → ∀ xs → foldr _•ᵃ_ e (map f xs) ≈  f (foldr _•ᵇ_ d xs)
  foldr-map-commute _       _      e≈fd []       = e≈fd
  foldr-map-commute •ᵃ-cong f-cong e≈fd (x ∷ xs) =
    ≈-trans (•ᵃ-cong ≈-refl (foldr-map-commute •ᵃ-cong f-cong e≈fd xs)) (f-cong x _)
