open import Data.List hiding (any; head; tail)
open import Data.List.All as All using (All; []; _∷_; head; tail; universal)
open import Data.List.All.Properties
open import Data.List.Any using (here; there)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _≤_; _<_)
open import Data.Fin using (Fin)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; REL; Total; Setoid; _Respects_; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst; subst₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Function using (_∘_; id)
open import Algebra.FunctionProperties using (Op₂; Congruent₂)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Properties
open import RoutingLib.Data.Fin.Properties using (𝔽ₛ)

module RoutingLib.Data.List.All.Properties where

------------------------------------------------------------------------
-- Miscaellaneous

module _ {a b ℓ} {A : Set a} {B : Set b} where

  All-swap : ∀ {_~_ : REL (List A) B ℓ} {xss ys} →
             All (λ xs → All (xs ~_) ys) xss →
             All (λ y → All (_~ y) xss) ys
  All-swap {ys = []}      _  = []
  All-swap {ys = _ ∷ _}  []  = universal (λ _ → []) _
  All-swap {ys = y ∷ ys} ((x~y ∷ x~ys) ∷ pxss) =
    (x~y ∷ (All.map head pxss)) ∷ All-swap (x~ys ∷ (All.map tail pxss))

------------------------------------------------------------------------
-- map

module _ {a b p} {A : Set a} {B : Set b} {P : A → Set p} {f : B → A} where

  map⁺₂ : (∀ x → P (f x)) → ∀ xs → All P (map f xs)
  map⁺₂ Pf []       = []
  map⁺₂ Pf (x ∷ xs) = Pf x ∷ map⁺₂ Pf xs

------------------------------------------------------------------------
-- insert

module _ {a ℓ} {A : Set a} {_≤_ : Rel A ℓ} (total : Total _≤_)
         {p} {P : Pred A p} where

  insert⁺ : ∀ {v xs} → P v → All P xs → All P (insert total v xs)
  insert⁺ {v} {[]}    pv []         = pv ∷ []
  insert⁺ {v} {x ∷ _} pv (px ∷ pxs) with total v x
  ... | inj₁ v≤x = pv ∷ (px ∷ pxs)
  ... | inj₂ x≤v = px ∷ (insert⁺ pv pxs)

  insert⁻ : ∀ v xs → All P (insert total v xs) → P v × All P xs
  insert⁻ v []       (pv ∷ []) = pv , []
  insert⁻ v (x ∷ xs) pvxxs      with total v x | pvxxs
  ... | inj₁ _ | pv ∷ (px ∷ pxs) = pv , px ∷ pxs
  ... | inj₂ _ | px ∷ pvxs       = Prod.map id (px ∷_) (insert⁻ v xs pvxs)
{-
------------------------------------------------------------------------
-- applyBetween

module _ {a p} {A : Set a} {P : A → Set p} where

  applyBetween⁺₁ : ∀ f s e → (∀ {i} → s ≤ i → i < e → P (f i)) → All P (applyBetween f s e)
  applyBetween⁺₁ f zero    e       Pf = applyUpTo⁺₁ f e (Pf z≤n)
  applyBetween⁺₁ f (suc s) zero    Pf = []
  applyBetween⁺₁ f (suc s) (suc e) Pf = applyBetween⁺₁ (f ∘ suc) s e (λ s≤i i<e → Pf (s≤s s≤i) (s≤s i<e))

  applyBetween⁺₂ : ∀ f s e → (∀ {i} → P (f i)) → All P (applyBetween f s e)
  applyBetween⁺₂ f s e Pf = applyBetween⁺₁ f s e (λ _ _ → Pf)

------------------------------------------------------------------------
-- between

s≤betweenₛₑ : ∀ s e → All (s ≤_) (between s e)
s≤betweenₛₑ s e = All-applyBetween⁺₁ id s e (λ s≤i _ → s≤i)

betweenₛₑ<e : ∀ s e → All (_< e) (between s e)
betweenₛₑ<e s e = All-applyBetween⁺₁ id s e (λ _ i<e → i<e)
-}

------------------------------------------------------------------------
-- deduplicate

module _ {a ℓ} (DS : DecSetoid a ℓ) where

  open DecSetoid DS renaming (Carrier to A)
  open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
  open import Data.List.Membership.DecSetoid DS using (_∈?_)

  deduplicate⁺ : ∀ {p} {P : A → Set p} {xs} → All P xs → All P (deduplicate xs)
  deduplicate⁺ {xs = _}      [] = []
  deduplicate⁺ {xs = x ∷ xs} (px ∷ pxs) with x ∈? xs
  ... | yes _ = deduplicate⁺ pxs
  ... | no  _ = px ∷ deduplicate⁺ pxs


module _ {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  open import Data.List.Membership.Setoid S using (_∈_)

  ∈-All : ∀ {p} {P : A → Set p} xs → (∀ {v} → v ∈ xs → P v) → All P xs
  ∈-All []       _   = []
  ∈-All (x ∷ xs) ∈⇨P = ∈⇨P (here refl) ∷ ∈-All xs (∈⇨P ∘ there)

  All-∈ : ∀ {p} {P : A → Set p} → P Respects _≈_ → ∀ {v xs} → All P xs → v ∈ xs → P v
  All-∈ resp (px ∷ pxs) (here v≈x)   = resp (sym v≈x) px
  All-∈ resp (px ∷ pxs) (there v∈xs) = All-∈ resp pxs v∈xs

  map-all : ∀ {b p} {B : Set b} {P : B → Set p} f {xs : List A} →
            (∀ {x} → x ∈ xs → P (f x)) → All P (map f xs)
  map-all f {[]}     pres = []
  map-all f {x ∷ xs} pres = pres (here refl) ∷ map-all f (pres ∘ there)





module _ {a₁ ℓ₁} (S₁ : Setoid a₁ ℓ₁)
         {a₂ ℓ₂} (S₂ : Setoid a₂ ℓ₂) where

  open Setoid S₁ renaming (Carrier to A₁; refl to refl₁)
  open Setoid S₂ renaming (Carrier to A₂)

  open import Data.List.Membership.Setoid S₁ using () renaming (_∈_ to _∈₁_)
  open import Data.List.Membership.Setoid S₂ using () renaming (_∈_ to _∈₂_)

  combine⁺ : ∀ {b p} {B : Set b} {P : B → Set p} _•_ (xs : List A₁) (ys : List A₂) →
             (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (x • y)) → All P (combine _•_ xs ys)
  combine⁺ _•_ []       ys pres = []
  combine⁺ _•_ (x ∷ xs) ys pres =
    ++⁺ (map-all S₂ (x •_) (pres (here refl₁))) (combine⁺ _•_ xs ys (pres ∘ there))


allFinPairs⁺ : ∀ {n p} {P : Pred (Fin n × Fin n) p} →
               (∀ e → P e) → All P (allFinPairs n)
allFinPairs⁺ {n} P = combine⁺ (𝔽ₛ n) (𝔽ₛ n) _,_ (allFin n) (allFin n) (λ _ _ → P _)
