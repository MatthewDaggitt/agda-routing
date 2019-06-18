open import Algebra
open import Algebra.FunctionProperties
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-suc)
open import Data.List
open import Data.List.Properties
open import Data.List.All using (All; []; _∷_; universal)
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Unary using (Decidable; Pred; ∁)
open import Relation.Unary.Properties using (∁?)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans)
open import Function using (id; _∘_)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (¬_)
open import Relation.Unary using (∁; U)
open import Relation.Unary.Properties using (U-Universal)

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
-- Properties of lookup

module _ {a} {A : Set a} where

  lookup∈xs : ∀ (xs : List A) (i : Fin (length xs)) → lookup xs i ∈ xs
  lookup∈xs (x ∷ xs) zero    = here refl
  lookup∈xs (x ∷ xs) (suc i) = there (lookup∈xs xs i)

------------------------------------------------------------------------
-- Semilattice properties

module _ {a ℓ} (S : Semilattice a ℓ)  where

  open Semilattice S renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open import Data.List.Membership.Setoid setoid using () renaming (_∈_ to _∈ₛ_)
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Relation.Binary.Construct.NaturalOrder.Right _≈_ _∧_ renaming (_≤_ to _≤ᵣ_)
  open import Relation.Binary.Construct.NaturalOrder.Left _≈_ _∧_ renaming (_≤_ to _≤ₗ_)

  foldr≤ᵣe : ∀ e xs → foldr _∧_ e xs ≤ᵣ e
  foldr≤ᵣe e [] = ≈-sym (idem e)
  foldr≤ᵣe e (x ∷ xs) = ≈-sym (begin
    e ∧ (x  ∧ foldr _∧_ e xs)  ≈⟨ ≈-sym (assoc e x _) ⟩
    (e ∧ x) ∧ foldr _∧_ e xs   ≈⟨ ∧-congʳ (comm e x) ⟩
    (x ∧ e) ∧ foldr _∧_ e xs   ≈⟨ assoc x e _ ⟩
    x ∧ (e  ∧ foldr _∧_ e xs)  ≈⟨ ∧-congˡ (≈-sym (foldr≤ᵣe e xs)) ⟩
    x       ∧ foldr _∧_ e xs   ∎)

  foldr≤ₗe : ∀ e xs → foldr _∧_ e xs ≤ₗ e
  foldr≤ₗe e xs = ≈-trans (foldr≤ᵣe e xs) (comm e _)

  foldr≤ᵣxs : ∀ e {x xs} → x ∈ₛ xs → foldr _∧_ e xs ≤ᵣ x
  foldr≤ᵣxs e {x} {y ∷ xs} (here x≈y) = ≈-sym (begin
    x ∧ (y  ∧ foldr _∧_ e xs) ≈⟨ ≈-sym (assoc x y _) ⟩
    (x ∧ y) ∧ foldr _∧_ e xs  ≈⟨ ∧-congʳ (∧-cong x≈y ≈-refl) ⟩
    (y ∧ y) ∧ foldr _∧_ e xs  ≈⟨ ∧-congʳ (idem y) ⟩
    y       ∧ foldr _∧_ e xs  ∎)
  foldr≤ᵣxs e {x} {y ∷ xs} (there x∈xs) = ≈-sym (begin
    x ∧ (y ∧ foldr _∧_ e xs)  ≈⟨ ≈-sym (assoc x y _) ⟩
    (x ∧ y) ∧ foldr _∧_ e xs  ≈⟨ ∧-congʳ (comm x y) ⟩
    (y ∧ x) ∧ foldr _∧_ e xs  ≈⟨ assoc y x _ ⟩
    y ∧ (x ∧ foldr _∧_ e xs)  ≈⟨ ∧-congˡ (≈-sym (foldr≤ᵣxs e x∈xs)) ⟩
    y ∧ foldr _∧_ e xs        ∎)

  foldr≤ₗxs : ∀ e {x xs} → x ∈ₛ xs → foldr _∧_ e xs ≤ₗ x
  foldr≤ₗxs e x∈xs = ≈-trans (foldr≤ᵣxs e x∈xs) (comm _ _)


module _ {a ℓ} (S : Setoid a ℓ)  where

  open Setoid S renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open EqReasoning S

  foldr-map-commute-gen₁ : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} → Congruent₂ _≈_ _•ᵃ_ →
                           ∀ {p} {P : Pred B p} → _•ᵇ_ Preservesᵇ P →
                           (∀ {x y} → P x → P y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                           ∀ {d : B} {xs : List B} → P d → All P xs →
                           foldr _•ᵃ_ (f d) (map f xs) ≈ f (foldr _•ᵇ_ d xs)
  foldr-map-commute-gen₁ cong •-pres-P P-pres-f pd []         = ≈-refl
  foldr-map-commute-gen₁ cong •-pres-P P-pres-f pd (px ∷ pxs) = ≈-trans
    (cong ≈-refl (foldr-map-commute-gen₁ cong •-pres-P P-pres-f pd pxs))
    (P-pres-f px (foldr-preservesᵇ •-pres-P pd pxs))

  foldr-map-commute-gen₂ : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} → Congruent₂ _≈_ _•ᵃ_ →
                           ∀ {ℓ} {_~_ : Rel B ℓ} → (∀ {x} → _•ᵇ_ Preservesᵇ (x ~_)) →
                           (∀ {x y} → x ~ y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                           ∀ {d : B} {xs : List B} → All (_~ d) xs → AllPairs _~_ xs →
                           foldr _•ᵃ_ (f d) (map f xs) ≈ f (foldr _•ᵇ_ d xs)
  foldr-map-commute-gen₂ {_}           {_}    {_} cong •ᵇ-pres-~ ~-pres-f {_} pd []       = ≈-refl
  foldr-map-commute-gen₂ {_•ᵃ_ = _•ᵃ_} {_•ᵇ_} {f} cong {_} {_~_} •ᵇ-pres-~ ~-pres-f {d} {x ∷ xs} (x~d ∷ xs~d) (px ∷ pxs) = begin
    (f x •ᵃ foldr _•ᵃ_ (f d) (map f xs)) ≈⟨ cong ≈-refl (foldr-map-commute-gen₂ cong •ᵇ-pres-~ ~-pres-f xs~d pxs) ⟩
    (f x •ᵃ f (foldr _•ᵇ_ d xs))         ≈⟨ ~-pres-f (foldr-preservesᵇ •ᵇ-pres-~ x~d px) ⟩
    f (x •ᵇ foldr _•ᵇ_ d xs)             ∎

  foldr-map-commute : ∀ {b} {B : Set b} {_•ᵃ_ _•ᵇ_} {f : B → A} →
                      Congruent₂ _≈_ _•ᵃ_ →
                      (∀ x y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                      ∀ d xs → foldr _•ᵃ_ (f d) (map f xs) ≈  f (foldr _•ᵇ_ d xs)
  foldr-map-commute cong pres d xs = foldr-map-commute-gen₁ cong (λ _ _ → _) (λ _ _ → pres _ _) (U-Universal d) (universal U-Universal xs)
