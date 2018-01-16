open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to mapₛ)
open import Data.Product using (∃; _×_; _,_) renaming (map to mapₚ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List
open import Data.List.Any as Any using (Any; here; there; index)
open import Data.List.Any.Properties
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id; _∘_)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.List using (applyBetween; lookup)
open import RoutingLib.Data.List.Any
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List.Permutation using (_⇿_; _◂_≡_; here; there; []; _∷_)

module RoutingLib.Data.List.Any.Properties where

  Any-gfilter : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} (Q : A → Maybe B) → ∀ xs → Any (λ x → ∃ λ y → Q x ≡ just y × P y) xs → Any P (gfilter Q xs)
  Any-gfilter Q (x ∷ xs) (here (y , Qx≡y , Py)) with Q x
  ... | nothing = contradiction Qx≡y λ()
  ... | just z  = here (subst _ (just-injective (sym Qx≡y)) Py)
  Any-gfilter Q (x ∷ xs) (there Pxs) with Q x
  ... | nothing = Any-gfilter Q xs Pxs
  ... | just z  = there (Any-gfilter Q xs Pxs)



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


    Any-applyBetween⁺ : ∀ f {s e i} → s ≤ i → i < e → P (f i) → Any P (applyBetween f s e)
    Any-applyBetween⁺ f z≤n       (s≤s i<e) Pf₀ = applyUpTo⁺ f Pf₀ (s≤s i<e)
    Any-applyBetween⁺ f (s≤s s≤i) (s≤s i<e) Pfᵢ = Any-applyBetween⁺ (f ∘ suc) s≤i i<e Pfᵢ

    Any-applyBetween⁻ : ∀ f s e → Any P (applyBetween f s e) → ∃ λ i → s ≤ i × i < e × P (f i)
    Any-applyBetween⁻ f zero    _       pxs = mapₚ id (z≤n ,_) (applyUpTo⁻ f pxs)
    Any-applyBetween⁻ f (suc s) zero    ()
    Any-applyBetween⁻ f (suc s) (suc e) pxs with Any-applyBetween⁻ (f ∘ suc) s e pxs
    ... | i , s≤i , i<e , Pfᵢ = suc i , s≤s s≤i , s≤s i<e , Pfᵢ



  module _ {a p} {A : Set a} {P : Pred A p} where


    lookup-index : ∀ {xs} (p : Any P xs) → P (lookup xs (index p))
    lookup-index (here px)   = px
    lookup-index (there pxs) = lookup-index pxs
    
{-
    index-cong : ∀ {x y xs} → x ≈ y → (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → Unique S xs → indexOf x∈xs ≡ indexOf y∈xs
    index-cong x≈y (here x≈z)   (here y≈z)   _            = refl
    index-cong x≈y (here x≈z)   (there y∈xs) (z≉xs ∷ xs!) = contradiction (∈-resp-≈ y∈xs (trans (sym x≈y) x≈z)) (All¬⇒¬Any z≉xs)
    index-cong x≈y (there x∈xs) (here y≈z)   (z≉xs ∷ xs!) = contradiction (∈-resp-≈ x∈xs (trans x≈y y≈z)) (All¬⇒¬Any z≉xs)
    index-cong x≈y (there x∈xs) (there y∈xs) (_ ∷ xs!)    = cong suc (indexOf-cong x≈y x∈xs y∈xs xs!)
-}

{-
    index-lookup : ∀ {xs} (pxs₁ pxs₂ : Any P xs) → index pxs₁ ≡ index pys₁ → x ≡ y
    index-lookup (here x≈z)   (here y≈z)   refl    = trans x≈z (sym y≈z)
    index-lookup (here x≈z)   (there y∈xs) ()
    index-lookup (there x∈xs) (here y≈z)   ()
    index (there x∈xs) (there y∈xs) indexEq = indexOf-revCong x∈xs y∈xs (suc-injective indexEq)

    index-lookup : ∀ {i xs} → Unique S xs → (i<|xs| : i < length xs) (xsᵢ∈xs : (lookup xs i<|xs|) ∈ xs) → indexOf xsᵢ∈xs ≡ i
    index-lookup {_}     []           ()     
    index-lookup {zero}  (_    ∷ _)   (s≤s i<|xs|) (here xsᵢ≈x)   = refl
    index-lookup {zero}  (x≉xs ∷ _)   (s≤s i<|xs|) (there x∈xs)  = contradiction x∈xs (All¬⇒¬Any x≉xs)
    index-lookup {suc i} (x≉xs ∷ _)   (s≤s i<|xs|) (here xsᵢ≈x)   = contradiction (∈-resp-≈ (∈-lookup i<|xs|) xsᵢ≈x) (All¬⇒¬Any x≉xs)
    index-lookup {suc i} (_    ∷ xs!) (s≤s i<|xs|) (there xsᵢ∈xs) = cong suc (indexOf-lookup xs! i<|xs| xsᵢ∈xs)
-}
