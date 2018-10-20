open import Data.List hiding (any)
open import Data.List.All as All using (All; []; _∷_)
import Data.List.All.Properties as All
open import Data.Nat using (zero; suc; _<_; z≤n; s≤s)
open import Function using (_∘_)
open import Relation.Binary using (Rel; Total; Symmetric; DecSetoid)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.AllPairs
import RoutingLib.Data.List.All.Properties as All
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.AllPairs.Properties where

-- All pairs

  {-
All⇒AllPairs : ∀ {a p ℓ} {A : Set a} {P : Pred A p} {_~_ : Rel A ℓ} {xs} →
                 All P xs → (∀ {x y} → P x → P y → x ~ y) → AllPairs _~_ xs
All⇒AllPairs []         pres = []
All⇒AllPairs (px ∷ pxs) pres = All.map (pres px) pxs ∷ (All⇒AllPairs pxs pres)

  AllPairs-map⁺₂ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}  {_~₁_ : Rel A ℓ₁} {_~₂_ : Rel B ℓ₂}
              {f : A → B} → f Preserves _~₁_ ⟶ _~₂_ → AllPairs _~₁_ ⋐ AllPairs _~₂_ ∘ map f
  AllPairs-map⁺₂ f-pres []           = []
  AllPairs-map⁺₂ f-pres (x∉xs ∷ xs!) = All-map (mapₐ f-pres x∉xs) ∷ AllPairs-map⁺₂ f-pres xs!
  -}

  {-
  AllPairs-mapMaybe⁺ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {_~₁_ : Rel A ℓ₁} {_~₂_ : Rel B ℓ₂}
                  (f : A → Maybe B) → (∀ {x y} → x ~₁ y → (f x ≡ nothing) ⊎ (f y ≡ nothing) ⊎ (Eq _~₂_ (f x) (f y)))
                  → AllPairs _~₁_ ⋐ AllPairs _~₂_ ∘ mapMaybe f
  AllPairs-mapMaybe⁺ _ _ [] = []
  AllPairs-mapMaybe⁺ {_~₁_ = _~₁_} {_~₂_} f f-inj {x ∷ xs} (px ∷ pxs) with f x | inspect f x
  ... | nothing | _            = AllPairs-mapMaybe⁺ f f-inj pxs
  ... | just v  | [ fx≡justv ] = mapMaybe⁺ (v ~₂_) {!!} ∷ AllPairs-mapMaybe⁺ f f-inj pxs
    where
    convert : ∀ {a} → x ~₁ a → ∀ {b} → f a ≡ just b → v ~₂ b
    convert {a} x~a {b} fa≡justb with f-inj x~a
    ... | inj₁ fx≡nothing        = contradiction (≡-trans (≡-sym fx≡nothing) fx≡justv) λ()
    ... | inj₂ (inj₁ fa≡nothing) = contradiction (≡-trans (≡-sym fa≡nothing) fa≡justb) λ()
    ... | inj₂ (inj₂ fx~fa)      = drop-just (subst₂ (Eq _~₂_) fx≡justv fa≡justb fx~fa)
  -}

------------------------------------------------------------------------
-- filter

module _ {a ℓ p} {A : Set a} {_~_ : Rel A ℓ}
         {P : Pred A p} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → AllPairs _~_ xs → AllPairs _~_ (filter P? xs)
  filter⁺ {_}      []           = []
  filter⁺ {x ∷ xs} (x∉xs ∷ xs!) with P? x
  ... | no  _ = filter⁺ xs!
  ... | yes _ = All.filter⁺₂ P? x∉xs ∷ filter⁺ xs!

------------------------------------------------------------------------
-- ++

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  ++⁺ : ∀ {xs ys} → AllPairs _~_ xs → AllPairs _~_ ys →
        All (λ x → All (x ~_) ys) xs → AllPairs _~_ (xs ++ ys)
  ++⁺ []         ~ys _              = ~ys
  ++⁺ (px ∷ ~xs) ~ys (x~ys ∷ xs~ys) = All.++⁺ px x~ys ∷ ++⁺ ~xs ~ys xs~ys

------------------------------------------------------------------------
-- concat

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  concat⁺ : ∀ {xss} → All (AllPairs _~_) xss →
            AllPairs (λ xs ys → All (λ x → All (x ~_) ys) xs) xss →
            AllPairs _~_ (concat xss)
  concat⁺ []           []              = []
  concat⁺ (pxs ∷ pxss) (xs~xss ∷ ~xss) = ++⁺ pxs (concat⁺ pxss ~xss)
    (All.map All.concat⁺ (All.All-swap xs~xss))

------------------------------------------------------------------------
-- drop

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  drop⁺ : ∀ {xs} n → AllPairs _~_ xs → AllPairs _~_ (drop n xs)
  drop⁺ zero    pxs       = pxs
  drop⁺ (suc n) []        = []
  drop⁺ (suc n) (_ ∷ pxs) = drop⁺ n pxs

------------------------------------------------------------------------
-- take

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  take⁺ : ∀ {xs} n → AllPairs _~_ xs → AllPairs _~_ (take n xs)
  take⁺ zero    pxs          = []
  take⁺ (suc n) []           = []
  take⁺ (suc n) (x~xs ∷ pxs) = All.take⁺ n x~xs ∷ (take⁺ n pxs)

------------------------------------------------------------------------
-- applyUpTo

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  applyUpTo⁺₁ : ∀ {f} n → (∀ {i j} → i < j → j < n → f i ~ f j) → AllPairs _~_ (applyUpTo f n)
  applyUpTo⁺₁ zero    f~ = []
  applyUpTo⁺₁ (suc n) f~ =
    All.applyUpTo⁺₁ _ n (f~ (s≤s z≤n) ∘ s≤s) ∷
    applyUpTo⁺₁ n (λ i≤j j<n → f~ (s≤s i≤j) (s≤s j<n))

  applyUpTo⁺₂ : ∀ f n → (∀ i j → f i ~ f j) → AllPairs _~_ (applyUpTo f n)
  applyUpTo⁺₂ f n f~ = applyUpTo⁺₁ n (λ _ _ → f~ _ _)

{-
------------------------------------------------------------------------
-- applyBetween

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where
  applyBetween⁺₁ : ∀ f s e → (∀ {i j} → s ≤ i → i < j → j < e → f i ~ f j) →
                   AllPairs _~_ (applyBetween f s e)
  applyBetween⁺₁ f zero    e       Pf = applyUpTo⁺₁ f e (Pf z≤n)
  applyBetween⁺₁ f (suc s) zero    Pf = []
  applyBetween⁺₁ f (suc s) (suc e) Pf =
    applyBetween⁺₁ (f ∘ suc) s e (λ s≤i i<j j<e → Pf (s≤s s≤i) (s≤s i<j) (s≤s j<e))

  applyBetween⁺₂ : ∀ f s e → (∀ {i j} → f i ~ f j) →
                   AllPairs _~_ (applyBetween f s e)
  applyBetween⁺₂ f s e Pf = applyBetween⁺₁ f s e (λ _ _ _ → Pf)

-}
------------------------------------------------------------------------
-- deduplicate

module _ {a ℓ} (DS : DecSetoid a ℓ) where

  open DecSetoid DS renaming (Carrier to A)
  open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
  open import Data.List.Membership.DecSetoid DS using (_∈?_)

  deduplicate⁺ : ∀ {ℓ} {_~_ : Rel A ℓ} {xs} → AllPairs _~_ xs →
                 AllPairs _~_ (deduplicate xs)
  deduplicate⁺ {xs = _}      [] = []
  deduplicate⁺ {xs = x ∷ xs} (px ∷ pxs) with x ∈? xs
  ... | yes _ = deduplicate⁺ pxs
  ... | no  _ = All.deduplicate⁺ DS px ∷ deduplicate⁺ pxs
