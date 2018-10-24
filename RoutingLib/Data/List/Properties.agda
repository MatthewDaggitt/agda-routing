open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-suc)
open import Data.List
open import Data.List.All using (All; []; _∷_; universal)
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Unary using (Decidable; Pred; ∁)
open import Relation.Unary.Properties using (∁?)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (∁; U)
open import Relation.Unary.Properties using (U-Universal)
open import Function using (id; _∘_)
open import Algebra using (Semilattice)
open import Algebra.FunctionProperties

open import RoutingLib.Algebra
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

module _ {a ℓ} (M : Magma a ℓ) where

  open Magma M
  open import Relation.Binary.EqReasoning setoid
  
  foldr-zeroʳ  : ∀ {e} → RightZero _≈_ e _∙_ → ∀ xs → foldr _∙_ e xs ≈ e
  foldr-zeroʳ {e} zeroʳ []       = Magma.refl M
  foldr-zeroʳ {e} zeroʳ (x ∷ xs) = begin
    x ∙ foldr _∙_ e xs ≈⟨ ∙-cong (Magma.refl M) (foldr-zeroʳ zeroʳ xs) ⟩
    x ∙ e              ≈⟨ zeroʳ x ⟩
    e                  ∎

  foldr-constant : ∀ {e} → _IdempotentOn_ _≈_ _∙_ e → ∀ {xs} → All (_≈ e) xs → foldr _∙_ e xs ≈ e
  foldr-constant {e} idem {[]}     []            = Magma.refl M
  foldr-constant {e} idem {x ∷ xs} (x≈e ∷ xs≈e) = begin
    x ∙ foldr _∙_ e xs ≈⟨ ∙-cong x≈e (foldr-constant idem xs≈e) ⟩
    e ∙ e              ≈⟨ idem ⟩
    e                  ∎
  
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

------------------------------------------------------------------------
-- Properties of applyUpTo

module _ {a} {A : Set a} where

  length-applyUpTo : ∀ (f : ℕ → A) n → length (applyUpTo f n) ≡ n
  length-applyUpTo f zero    = refl
  length-applyUpTo f (suc n) = cong suc (length-applyUpTo (f ∘ suc) n)

------------------------------------------------------------------------
-- Properties of upTo

length-upTo : ∀ n → length (upTo n) ≡ n
length-upTo = length-applyUpTo id
  
------------------------------------------------------------------------
-- Properties of applyDownFrom

module _ {a} {A : Set a} (f : ℕ → A) where

  length-applyDownFrom : ∀ n → length (applyDownFrom f n) ≡ n
  length-applyDownFrom zero    = refl
  length-applyDownFrom (suc n) = cong suc (length-applyDownFrom n)

  applyDownFrom-lookup : ∀ n i → lookup (applyDownFrom f n) i ≡ f (n ∸ (suc (toℕ i)))
  applyDownFrom-lookup zero  ()
  applyDownFrom-lookup (suc n) zero    = refl
  applyDownFrom-lookup (suc n) (suc i) = applyDownFrom-lookup n i
  
------------------------------------------------------------------------
-- Properties of downFrom

length-downFrom : ∀ n → length (downFrom n) ≡ n
length-downFrom = length-applyDownFrom id

downFrom-lookup : ∀ n i → lookup (downFrom n) i ≡ n ∸ (suc (toℕ i))
downFrom-lookup = applyDownFrom-lookup id

------------------------------------------------------------------------
-- Properties of lookup

module _ {a} {A : Set a} where

  lookup∈xs : ∀ (xs : List A) (i : Fin (length xs)) → lookup xs i ∈ xs
  lookup∈xs []       ()
  lookup∈xs (x ∷ xs) zero    = here refl
  lookup∈xs (x ∷ xs) (suc i) = there (lookup∈xs xs i)

------------------------------------------------------------------------
-- Properties of tabulate

module _ {a b} {A : Set a} {B : Set b} where

  map-tabulate : ∀ {n} (g : Fin n → A) (f : A → B) →
                 map f (tabulate g) ≡ tabulate (f ∘ g)
  map-tabulate {zero}  g f = refl
  map-tabulate {suc n} g f = cong (_ ∷_) (map-tabulate (g ∘ suc) f)

------------------------------------------------------------------------
-- Semilattice properties

module _ {a ℓ} (S : Semilattice a ℓ)  where

  open Semilattice S renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open import Data.List.Membership.Setoid setoid using () renaming (_∈_ to _∈ₛ_)
  open import Relation.Binary.EqReasoning setoid

  foldr≤ᵣe : ∀ e xs → e ∧ foldr _∧_ e xs ≈ foldr _∧_ e xs
  foldr≤ᵣe e [] = idem e
  foldr≤ᵣe e (x ∷ xs) = begin
    e ∧ (x ∧ foldr _∧_ e xs) ≈⟨ ≈-sym (assoc e x _) ⟩
    (e ∧ x) ∧ foldr _∧_ e xs ≈⟨ ∙-cong (comm e x) ≈-refl ⟩
    (x ∧ e) ∧ foldr _∧_ e xs ≈⟨ assoc x e _ ⟩
    x ∧ (e ∧ foldr _∧_ e xs) ≈⟨ ∙-cong ≈-refl (foldr≤ᵣe e xs) ⟩
    x ∧ foldr _∧_ e xs       ∎

  open import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right _≈_ _∧_ renaming (_≤_ to _≤ᵣ_)

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

  foldr-map-commute-gen : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} → Congruent₂ _≈_ _•ᵃ_ →
                          ∀ {p} {P : Pred B p} → _•ᵇ_ Preservesᵇ P →
                          (∀ {x y} → P x → P y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                          ∀ {d : B} {xs : List B} → P d → All P xs →
                          foldr _•ᵃ_ (f d) (map f xs) ≈ f (foldr _•ᵇ_ d xs)
  foldr-map-commute-gen cong •-pres-P P-pres-f pd []         = ≈-refl
  foldr-map-commute-gen cong •-pres-P P-pres-f pd (px ∷ pxs) = ≈-trans
    (cong ≈-refl (foldr-map-commute-gen cong •-pres-P P-pres-f pd pxs))
    (P-pres-f px (foldr-presᵇ •-pres-P pd pxs))

  foldr-map-commute : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} →
                      Congruent₂ _≈_ _•ᵃ_ →
                      (∀ x y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                      ∀ d xs → foldr _•ᵃ_ (f d) (map f xs) ≈  f (foldr _•ᵇ_ d xs)
  foldr-map-commute cong pres d xs = foldr-map-commute-gen cong (λ _ _ → _) (λ _ _ → pres _ _) (U-Universal d) (universal U-Universal xs)
