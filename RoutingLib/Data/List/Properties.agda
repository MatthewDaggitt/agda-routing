open import Algebra
-- open import Algebra.FunctionProperties
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-suc)
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise
  using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.AllPairs
  using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Unique.Setoid
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; Setoid; Trichotomous; tri<; tri≈; tri>; Reflexive)
open import Relation.Unary using (Decidable; Pred; ∁)
open import Relation.Unary.Properties using (∁?)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans)
open import Relation.Binary.Structures using (IsPreorder; IsEquivalence)
open import Function using (id; _∘_)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (¬_)
open import Relation.Unary using (∁; U; Pred)
open import Relation.Unary.Properties using (U-Universal)

open import RoutingLib.Data.List renaming (strictMerge to strictMerge')
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Algebra.Definitions

module RoutingLib.Data.List.Properties where

private
  variable
    a b p q ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Properties of filter

module _ {P : A → Set p} (P? : Decidable P) where

  filter-length₂ : ∀ xs → length (filter (∁? P?) xs) + length (filter P? xs) ≡ length xs
  filter-length₂ [] = refl
  filter-length₂ (x ∷ xs) with P? x
  ... | no  _ = cong suc (filter-length₂ xs)
  ... | yes _ = trans (+-suc (length (filter (∁? P?) xs)) (length (filter P? xs))) (cong suc (filter-length₂ xs))
  
------------------------------------------------------------------------
-- Properties of mapMaybe

module _ (f : A → Maybe B) where

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

module _ (M : Magma a ℓ) where

  open Magma M
  open import Relation.Binary.Reasoning.Setoid setoid

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

module _ {P : Pred A p} {_•_ : Op₂ A} where

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

lookup∈xs : ∀ (xs : List A) (i : Fin (length xs)) → lookup xs i ∈ xs
lookup∈xs (x ∷ xs) zero    = here refl
lookup∈xs (x ∷ xs) (suc i) = there (lookup∈xs xs i)

------------------------------------------------------------------------
-- Semilattice properties

module _ (S : Semilattice a ℓ)  where

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


module _ (S : Setoid a ℓ)  where

  open Setoid S renaming (Carrier to C; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open EqReasoning S

  foldr-map-commute-gen₁ : ∀ {_•ᵃ_ _•ᵇ_} {f : B → C} → Congruent₂ _≈_ _•ᵃ_ →
                           ∀ {p} {P : Pred B p} → _•ᵇ_ Preservesᵇ P →
                           (∀ {x y} → P x → P y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                           ∀ {d : B} {xs : List B} → P d → All P xs →
                           foldr _•ᵃ_ (f d) (map f xs) ≈ f (foldr _•ᵇ_ d xs)
  foldr-map-commute-gen₁ cong •-pres-P P-pres-f pd []         = ≈-refl
  foldr-map-commute-gen₁ cong •-pres-P P-pres-f pd (px ∷ pxs) = ≈-trans
    (cong ≈-refl (foldr-map-commute-gen₁ cong •-pres-P P-pres-f pd pxs))
    (P-pres-f px (foldr-preservesᵇ •-pres-P pd pxs))

  foldr-map-commute-gen₂ : ∀ {_•ᵃ_ _•ᵇ_} {f : B → C} → Congruent₂ _≈_ _•ᵃ_ →
                           ∀ {ℓ} {_~_ : Rel B ℓ} → (∀ {x} → _•ᵇ_ Preservesᵇ (x ~_)) →
                           (∀ {x y} → x ~ y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                           ∀ {d : B} {xs : List B} → All (_~ d) xs → AllPairs _~_ xs →
                           foldr _•ᵃ_ (f d) (map f xs) ≈ f (foldr _•ᵇ_ d xs)
  foldr-map-commute-gen₂ {_}           {_}    {_} cong •ᵇ-pres-~ ~-pres-f {_} pd []       = ≈-refl
  foldr-map-commute-gen₂ {_•ᵃ_ = _•ᵃ_} {_•ᵇ_} {f} cong {_} {_~_} •ᵇ-pres-~ ~-pres-f {d} {x ∷ xs} (x~d ∷ xs~d) (px ∷ pxs) = begin
    (f x •ᵃ foldr _•ᵃ_ (f d) (map f xs)) ≈⟨ cong ≈-refl (foldr-map-commute-gen₂ cong •ᵇ-pres-~ ~-pres-f xs~d pxs) ⟩
    (f x •ᵃ f (foldr _•ᵇ_ d xs))         ≈⟨ ~-pres-f (foldr-preservesᵇ •ᵇ-pres-~ x~d px) ⟩
    f (x •ᵇ foldr _•ᵇ_ d xs)             ∎

  foldr-map-commute : ∀ {_•ᵃ_ _•ᵇ_} {f : B → C} →
                      Congruent₂ _≈_ _•ᵃ_ →
                      (∀ x y → f x •ᵃ f y ≈ f (x •ᵇ y)) →
                      ∀ d xs → foldr _•ᵃ_ (f d) (map f xs) ≈  f (foldr _•ᵇ_ d xs)
  foldr-map-commute cong pres d xs = foldr-map-commute-gen₁ cong (λ _ _ → _) (λ _ _ → pres _ _) (U-Universal d) (universal U-Universal xs)

------------------------------------------------------------------------
-- Properties of strictMerge

module _ {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂}
         {cmp : Trichotomous _≈_ _<_} {_⊕_ : Op₂ A} where

  strictMerge : List A → List A → List A
  strictMerge = strictMerge' cmp _⊕_

  _≋_ : Rel (List A) _
  _≋_ = Pointwise _≈_

  strictMerge-identityˡ : LeftIdentity _≡_ [] strictMerge
  strictMerge-identityˡ xs = refl

  strictMerge-identityʳ : RightIdentity _≡_ [] strictMerge
  strictMerge-identityʳ [] = refl
  strictMerge-identityʳ (x ∷ xs) = refl

  strictMerge-identity : Identity _≡_ [] strictMerge
  strictMerge-identity = (strictMerge-identityˡ , strictMerge-identityʳ)

  module _ (≈-refl : Reflexive _≈_) {_≈'_ : Rel A ℓ} (⊕-idem : Idempotent _≈'_ _⊕_) where
  
    strictMerge-idempotent : Idempotent (Pointwise _≈'_) strictMerge
    strictMerge-idempotent [] = []
    strictMerge-idempotent (x ∷ xs) with cmp x x
    ... | tri< _ x≠x _ = contradiction ≈-refl x≠x
    ... | tri≈ _ x=x _ = (⊕-idem x) ∷ (strictMerge-idempotent xs)
    ... | tri> _ x≠x _ = contradiction ≈-refl x≠x

  module _ (≈-isEquivalence : IsEquivalence _≈_) (<-isPreorder : IsPreorder _≈_ _<_) (⊕-cong : Congruent₂ _≈_ _⊕_) where

    open IsEquivalence ≈-isEquivalence renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
    open IsPreorder <-isPreorder renaming (∼-respˡ-≈ to <-respˡ-≈; ∼-respʳ-≈ to <-respʳ-≈)

    strictMerge-cong : ∀ {xs xs' ys ys'} → xs ≋ xs' → ys ≋ ys' →
                       strictMerge xs ys ≋ strictMerge xs' ys'
    strictMerge-cong [] ys=ys' = ys=ys'
    strictMerge-cong (x=x' ∷ xs=xs') [] = x=x' ∷ xs=xs'
    strictMerge-cong {x ∷ xs} {x' ∷ xs'} {y ∷ ys} {y' ∷ ys'} (x=x' ∷ xs=xs') (y=y' ∷ ys=ys')
      with cmp x y | cmp x' y'
        | strictMerge-cong xs=xs' (y=y' ∷ ys=ys')
        | strictMerge-cong xs=xs' ys=ys'
        | strictMerge-cong (x=x' ∷ xs=xs') ys=ys'
    ... | tri< _ _   _ | tri< _ _     _ | rec₁ | _    | _    = x=x' ∷ rec₁
    ... | tri< _ x≠y _ | tri≈ _ x'=y' _ | _    | _    | _    = contradiction (≈-trans (≈-trans x=x' x'=y') (≈-sym y=y')) x≠y
    ... | tri< x<y _ _ | tri> x'≮y' _ _ | _    | _    | _    = contradiction (<-respˡ-≈ x=x' (<-respʳ-≈ y=y' x<y)) x'≮y'
    ... | tri≈ _ x=y _ | tri< _ x'≠y' _ | _    | _    | _    = contradiction (≈-trans (≈-trans (≈-sym x=x') x=y) y=y') x'≠y'
    ... | tri≈ _ _   _ | tri≈ _ _     _ | _    | rec₂ | _    = (⊕-cong x=x' y=y') ∷ rec₂
    ... | tri≈ _ x=y _ | tri> _ x'≠y' _ | _    | _    | _    = contradiction (≈-trans (≈-trans (≈-sym x=x') x=y) y=y') x'≠y'
    ... | tri> x≮y _ _ | tri< x'<y' _ _ | _    | _    | _    = contradiction (<-respˡ-≈ (≈-sym x=x') (<-respʳ-≈ (≈-sym y=y') x'<y')) x≮y
    ... | tri> _ x≠y _ | tri≈ _ x'=y' _ | _    | _    | _    = contradiction (≈-trans (≈-trans x=x' x'=y') (≈-sym y=y')) x≠y
    ... | tri> _ _   _ | tri> _ _     _ | _    | _    | rec₃ = y=y' ∷ rec₃
