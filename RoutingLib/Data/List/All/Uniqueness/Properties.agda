open import Level using (_⊔_)
open import Data.Nat using (zero; suc; z≤n; s≤s; _≤_; _<_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; gfilter; filter; map; concat; _++_)
open import Data.List.Any using (here; there; module Membership)
open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties using (gmap)
open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.Vec using (toList; tabulate; allFin)
open import Function using (_∘_; id)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (subst; _≡_; inspect; [_]) renaming (setoid to ≡-setoid)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.List.All using (AllPairs; []; _∷_)
open import RoutingLib.Data.List.All.Properties using (All¬→¬Any; ¬Any→All¬; ++-all)
open import RoutingLib.Data.Vec.Properties using (∉⇒List-∉; ∉-tabulate)
open import RoutingLib.Data.Nat.Properties using (≤-antisym)
open import RoutingLib.Data.Fin.Properties using (suc≢zero; suc-injective)
open import RoutingLib.Data.Maybe.Base using (predBoolToMaybe)
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List.All.Uniqueness using (Unique)
open import RoutingLib.Data.List.Any.GenericMembership using (filter-pres-∉; ∉-resp-≈; Disjoint; ∈xs⇨∉ys; disjoint-contract₁; disjoint-concat; length-remove; ⊆-remove; ∈-remove; ∈-resp-≈)


module RoutingLib.Data.List.All.Uniqueness.Properties where

  module SingleSetoid {c ℓ} (S : Setoid c ℓ) where

    open Setoid S renaming (Carrier to A)
    open Membership S using (_∈_; _∉_; _⊆_)

    module DoubleSetoid {d ℓ₂} (T : Setoid d ℓ₂) where

      open Setoid T renaming (Carrier to B; _≈_ to _≈₂_)

      map! : ∀ {f} → (∀ {x y} → ¬ (x ≈ y) → ¬ (f x ≈₂ f y)) → ∀ {xs} → Unique S xs → Unique T (map f xs)
      map! _     [] = []
      map! f-inj (x∉xs ∷ xs!) = gmap (λ x≉y → f-inj x≉y) x∉xs ∷ map! f-inj xs!

    open DoubleSetoid public


  -- Preservation of uniqueness properties

    filter! : ∀ P {xs} → Unique S xs → Unique S (filter P xs)
    filter! _ [] = []
    filter! P {x ∷ xs} (x∉xs ∷ xs!) with predBoolToMaybe P x | inspect (predBoolToMaybe P) x
    ... | nothing | _  = filter! P xs!
    ... | just v  | [ t ] with P x
    ...   | false = contradiction t λ()
    ...   | true  = ¬Any→All¬ (filter-pres-∉ S P (∉-resp-≈ S (All¬→¬Any x∉xs) (reflexive (just-injective t)))) ∷ filter! P xs!

    ++! : ∀ {xs ys} → Unique S xs → Unique S ys → Disjoint S xs ys → Unique S (xs ++ ys)
    ++! [] []  _ = []
    ++! [] ys! _ = ys!
    ++! (x∉xs ∷ xs!) ys! x∷xs#ys = ++-all x∉xs (¬Any→All¬ (∈xs⇨∉ys S x∷xs#ys (here refl))) ∷ (++! xs! ys! (disjoint-contract₁ S x∷xs#ys))

    concat! : ∀ {xss} → All (Unique S) xss → AllPairs (Disjoint S) xss → Unique S (concat xss)
    concat!                    []                    _                  = []
    concat!                   ([]       ∷ xss!)      (_ ∷ xss-dj)       = concat! xss! xss-dj
    concat! {(x ∷ xs) ∷ xss}  ((x∉xs ∷ xs!) ∷ xss!) (x∷xs-dj ∷ xss-dj)  = ++-all x∉xs (¬Any→All¬ (∈xs⇨∉ys S (disjoint-concat S x∷xs-dj) (here refl))) ∷ concat! (xs! ∷ xss!) ((mapₐ (disjoint-contract₁ S) x∷xs-dj) ∷ xss-dj)

    tabulate! : ∀ {a n} {A : Set a} (f : Fin n → A) → (∀ {i j} → f i ≡ f j → i ≡ j) → Unique (≡-setoid A) (toList (tabulate f))
    tabulate! {n = zero} f _ = []
    tabulate! {n = suc n} f f-inj = ¬Any→All¬ (∉⇒List-∉ (∉-tabulate (f ∘ fsuc) (λ _ → suc≢zero ∘ f-inj))) ∷ (tabulate! (f ∘ fsuc) (suc-injective ∘ f-inj))

    -- Other

    length-⊆ : ∀ {xs ys} → Unique S xs → xs ⊆ ys → length xs ≤ length ys 
    length-⊆                    []          _     = z≤n
    length-⊆ {_}      {[]}      (_ ∷ _)     xs⊆ys = contradiction (xs⊆ys (here refl)) λ()
    length-⊆ {x ∷ xs} {y ∷ ys} (x∉xs ∷ xs!) xs⊆ys = subst (λ v → length (x ∷ xs) ≤ v) (length-remove S (xs⊆ys (here refl))) (s≤s (length-⊆ xs! (⊆-remove S (xs⊆ys ∘ there) (xs⊆ys (here refl)) (All¬→¬Any x∉xs))))

    length-⊂ : ∀ {v xs ys} → Unique S xs → xs ⊆ ys → v ∉ xs → v ∈ ys → length xs < length ys
    length-⊂               {ys = []}     _              _        _      ()    
    length-⊂ {xs = []}     {ys = y ∷ ys} _              _        _      _    = s≤s z≤n
    length-⊂ {xs = x ∷ xs}               (x∉xs ∷ xs!)   x∷xs⊆ys v∉x∷xs v∈ys = subst (length (x ∷ xs) <_) (length-remove S (x∷xs⊆ys (here refl))) (s≤s (length-⊂ xs! (⊆-remove S (x∷xs⊆ys ∘ there) (x∷xs⊆ys (here refl)) (All¬→¬Any x∉xs)) (λ v∈xs → v∉x∷xs (there v∈xs)) (∈-remove S (x∷xs⊆ys (here refl)) v∈ys (λ x≈v → v∉x∷xs (∈-resp-≈ S (here refl) x≈v))) )) 

    length-⊆-⊇ : ∀ {xs ys} → Unique S xs → Unique S ys → xs ⊆ ys → ys ⊆ xs → length xs ≡ length ys
    length-⊆-⊇ xs! ys! xs⊆ys ys⊆xs = ≤-antisym (length-⊆ xs! xs⊆ys) (length-⊆ ys! ys⊆xs)

  open SingleSetoid public


  allFin! : ∀ n → Unique (≡-setoid (Fin n)) (toList (allFin n)) 
  allFin! n = tabulate! (≡-setoid (Fin n)) id id
