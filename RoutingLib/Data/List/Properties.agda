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
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Level using (Level; _⊔_)
open import Relation.Binary as B using (Rel; Setoid; Trichotomous; tri<; tri≈; tri>; Reflexive; Irreflexive; Asymmetric)
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

open import RoutingLib.Data.List renaming (partialMerge to partialMerge')
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
-- Properties of partialMerge

module _ {_<_ : Rel A ℓ₂} {_<?_ : B.Decidable _<_} {_⊕_ : Op₂ A} where

  partialMerge : List A → List A → List A
  partialMerge = partialMerge' _<?_ _⊕_

  partialMerge-identityˡ : LeftIdentity _≡_ [] partialMerge
  partialMerge-identityˡ xs = refl

  partialMerge-identityʳ : RightIdentity _≡_ [] partialMerge
  partialMerge-identityʳ [] = refl
  partialMerge-identityʳ (x ∷ xs) = refl

  partialMerge-identity : Identity _≡_ [] partialMerge
  partialMerge-identity = (partialMerge-identityˡ , partialMerge-identityʳ)
  
  partialMerge-∷-eq : ∀ {x xs y ys} → ¬ (x < y) → ¬ (y < x) → partialMerge (x ∷ xs) (y ∷ ys) ≡ (x ⊕ y) ∷ partialMerge xs ys
  partialMerge-∷-eq {x} {xs} {y} {ys} ¬x<y ¬y<x with x <? y | y <? x
  ... | yes x<y  | _       = contradiction x<y ¬x<y
  ... | no  _    | yes y<x = contradiction y<x ¬y<x
  ... | no  _    | no  _   = refl

  module _ (<-asym : Asymmetric _<_) where
    partialMerge-∷ˡ-min : ∀ {x xs ys} → All (x <_) ys → partialMerge (x ∷ xs) ys ≡ x ∷ (partialMerge xs ys)
    partialMerge-∷ˡ-min {x} {[]}    {[]}     []           = refl
    partialMerge-∷ˡ-min {x} {_ ∷ _} {[]}     []           = refl
    partialMerge-∷ˡ-min {x} {xs}    {y ∷ ys} (x<y ∷ x<ys) with x <? y | y <? x
    ... | yes _   | yes y<x = contradiction y<x (<-asym x<y)
    ... | yes _   | no  _   = refl
    ... | no ¬x<y | _       = contradiction x<y ¬x<y
  
    partialMerge-∷ʳ-min : ∀ {xs y ys} → All (y <_) xs → partialMerge xs (y ∷ ys) ≡ y ∷ (partialMerge xs ys)
    partialMerge-∷ʳ-min {[]}     {y} {ys} []           = refl
    partialMerge-∷ʳ-min {x ∷ xs} {y} {ys} (y<x ∷ y<xs) with x <? y | y <? x
    ... | yes x<y  | _       = contradiction y<x (<-asym x<y)
    ... | no  ¬x<y | yes _   = refl
    ... | no  ¬x<y | no ¬y<x = contradiction y<x ¬y<x
  
  module _ {_≈_ : Rel A ℓ₁} (≈-refl : Reflexive _≈_) (<-irrefl : Irreflexive _≈_ _<_)
           {_≈'_ : Rel A ℓ} (⊕-idem : Idempotent _≈'_ _⊕_) where
  
    partialMerge-idempotent : Idempotent (Pointwise _≈'_) partialMerge
    partialMerge-idempotent [] = []
    partialMerge-idempotent (x ∷ xs) with x <? x
    ... | yes x<x = contradiction x<x (<-irrefl ≈-refl)
    ... | no  _   = ⊕-idem x ∷ partialMerge-idempotent xs

  module _ {_≈_ : Rel A ℓ₁} (≈-isEquivalence : IsEquivalence _≈_)
           (<-resp-≈ : _<_ B.Respects₂ _≈_) (⊕-cong : Congruent₂ _≈_ _⊕_) where

    open IsEquivalence ≈-isEquivalence renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
    open SetoidEquality (record {isEquivalence = ≈-isEquivalence}) using (_≋_)

    <-resp₂-≈ : ∀ {w x y z} → w ≈ y → x ≈ z → w < x → y < z
    <-resp₂-≈ w≈y x≈z w<x = proj₂ <-resp-≈ w≈y (proj₁ <-resp-≈ x≈z w<x)
    
    partialMerge-cong : ∀ {xs xs' ys ys'} → xs ≋ xs' → ys ≋ ys' →
                       partialMerge xs ys ≋ partialMerge xs' ys'
    partialMerge-cong [] ys=ys' = ys=ys'
    partialMerge-cong (x=x' ∷ xs=xs') [] = x=x' ∷ xs=xs'
    partialMerge-cong {x ∷ xs} {x' ∷ xs'} {y ∷ ys} {y' ∷ ys'} (x=x' ∷ xs=xs') (y=y' ∷ ys=ys')
      with x <? y | y <? x | x' <? y' | y' <? x'
        | partialMerge-cong xs=xs' (y=y' ∷ ys=ys')
        | partialMerge-cong xs=xs' ys=ys'
        | partialMerge-cong (x=x' ∷ xs=xs') ys=ys'
    ... | yes _   | _       | yes _     | _         | rec₁ | _    | _    = x=x' ∷ rec₁
    ... | no  x≮y | _       | yes x'<y' | _         | _    | _    | _    = contradiction (<-resp₂-≈ (≈-sym x=x') (≈-sym y=y') x'<y') x≮y
    ... | yes x<y | _       | no  x'≮y' | _         | _    | _    | _    = contradiction (<-resp₂-≈ x=x' y=y' x<y) x'≮y'
    ... | no  _   | yes _   | no  _     | yes _     | _    | _    | rec₃ = y=y' ∷ rec₃
    ... | no  _   | no  y≮x | no  _     | yes y'<x' | _    | _    | _    = contradiction (<-resp₂-≈ (≈-sym y=y') (≈-sym x=x') y'<x') y≮x
    ... | no  _   | yes y<x | no  _     | no  y'≮x' | _    | _    | _    = contradiction (<-resp₂-≈ y=y' x=x' y<x) y'≮x'
    ... | no  _   | no  _   | no  _     | no _      | _    | rec₂ | _    = ⊕-cong x=x' y=y' ∷ rec₂
