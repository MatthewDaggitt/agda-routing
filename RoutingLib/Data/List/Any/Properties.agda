open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to mapₛ)
open import Data.Product using (∃; _×_; _,_) renaming (map to mapₚ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List
open import Data.List.Any as Any using (Any; here; there; index)
open import Data.List.Any.Properties
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; just-injective)
open import Function using (id; _∘_)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.List using (applyBetween)
open import RoutingLib.Data.List.Permutation using (_⇿_; _◂_≡_; here; there; []; _∷_)

module RoutingLib.Data.List.Any.Properties where


  module _ {a p} {A : Set a} {P : A → Set p} where

    -- Permutations

    Any-◂≡ : ∀ {x xs ys} → Any P (x ∷ xs) → x ◂ xs ≡ ys → Any P ys
    Any-◂≡ pxs                 here             = pxs
    Any-◂≡ (here px)           (there x◂xs≡xss) = there (Any-◂≡ (here px) x◂xs≡xss)
    Any-◂≡ (there (here py))   (there x◂xs≡xss) = here py
    Any-◂≡ (there (there pxs)) (there x◂xs≡xss) = there (Any-◂≡ (there pxs) x◂xs≡xss)
  
    Any-⇿ : ∀ {xs ys} → Any P xs → xs ⇿ ys → Any P ys
    Any-⇿ (here px)   (x◂zs≡ys ∷ xs⇿zs) = Any-◂≡ (here px) x◂zs≡ys
    Any-⇿ (there pxs) (x◂zs≡ys ∷ xs⇿zs) = Any-◂≡ (there (Any-⇿ pxs xs⇿zs)) x◂zs≡ys


    Any-applyBetween⁺ : ∀ f {s e i} → s ≤ i → i < e → P (f i) →
                        Any P (applyBetween f s e)
    Any-applyBetween⁺ f z≤n       (s≤s i<e) Pf₀ = applyUpTo⁺ f Pf₀ (s≤s i<e)
    Any-applyBetween⁺ f (s≤s s≤i) (s≤s i<e) Pfᵢ = Any-applyBetween⁺ (f ∘ suc) s≤i i<e Pfᵢ

    Any-applyBetween⁻ : ∀ f s e → Any P (applyBetween f s e) →
                        ∃ λ i → s ≤ i × i < e × P (f i)
    Any-applyBetween⁻ f zero    _       pxs = mapₚ id (z≤n ,_) (applyUpTo⁻ f pxs)
    Any-applyBetween⁻ f (suc s) zero    ()
    Any-applyBetween⁻ f (suc s) (suc e) pxs with Any-applyBetween⁻ (f ∘ suc) s e pxs
    ... | i , s≤i , i<e , Pfᵢ = suc i , s≤s s≤i , s≤s i<e , Pfᵢ



  module _ {a p} {A : Set a} {P : Pred A p} where


    lookup-index : ∀ {xs} (p : Any P xs) → P (lookup xs (index p))
    lookup-index (here px)   = px
    lookup-index (there pxs) = lookup-index pxs
