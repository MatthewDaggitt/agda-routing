open import Data.List hiding (any; head; tail)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_; head; tail; universal)
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _≤_; _<_)
open import Data.Fin using (Fin)
open import Data.Product as Prod using (_×_; _,_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; REL; Total; Setoid; _Respects_; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Function using (_∘_; id)

open import RoutingLib.Data.List
open import RoutingLib.Data.Fin.Properties using (𝔽ₛ)

module RoutingLib.Data.List.Relation.Unary.All.Properties where

------------------------------------------------------------------------
-- map

module _ {a b p} {A : Set a} {B : Set b} {P : A → Set p} {f : B → A} where

  map⁺₂ : (∀ x → P (f x)) → ∀ xs → All P (map f xs)
  map⁺₂ Pf []       = []
  map⁺₂ Pf (x ∷ xs) = Pf x ∷ map⁺₂ Pf xs
{-# WARNING_ON_USAGE map⁺₂
"Use All.universal instead"
#-}

------------------------------------------------------------------------
-- other

module _ {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  open import Data.List.Membership.Setoid S using (_∈_)

  ∈-All : ∀ {p} {P : A → Set p} xs → (∀ {v} → v ∈ xs → P v) → All P xs
  ∈-All []       _   = []
  ∈-All (x ∷ xs) ∈⇨P = ∈⇨P (here refl) ∷ ∈-All xs (∈⇨P ∘ there)

  All-∈ : ∀ {p} {P : A → Set p} → P Respects _≈_ → ∀ {v xs} → All P xs → v ∈ xs → P v
  All-∈ resp (px ∷ pxs) (here v≈x)   = resp (sym v≈x) px
  All-∈ resp (px ∷ pxs) (there v∈xs) = All-∈ resp pxs v∈xs

  -- map+ and All.tabulate
  map-all : ∀ {b p} {B : Set b} {P : B → Set p} f {xs : List A} →
            (∀ {x} → x ∈ xs → P (f x)) → All P (map f xs)
  map-all f {[]}     pres = []
  map-all f {x ∷ xs} pres = pres (here refl) ∷ map-all f (pres ∘ there)
{-# WARNING_ON_USAGE map-all
"Use map⁺ and All.tabulate"
#-}

allFinPairs⁺ : ∀ {n p} {P : Pred (Fin n × Fin n) p} →
               (∀ e → P e) → All P (allFinPairs n)
allFinPairs⁺ {n} P = cartesianProduct⁺ (𝔽ₛ n) (𝔽ₛ n) (allFin n) (allFin n) (λ _ _ → P _)
