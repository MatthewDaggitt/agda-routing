open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to mapₛ)
open import Data.Product using (∃; _×_; _,_) renaming (map to mapₚ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Any.Properties using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id; _∘_)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary.Negation using (contradiction)

open Any.Membership-≡ using (_∈_)
open import RoutingLib.Data.List.Any
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List
open import RoutingLib.Data.List.Permutation using (_⇿_; _◂_≡_; here; there; []; _∷_)
open import RoutingLib.Data.Nat.Properties using (suc-injective)

module RoutingLib.Data.List.Any.Properties where


  -- stdlib
  Any-map⁺ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
               {f : A → B} {xs} → Any (P ∘ f) xs → Any P (map f xs)
  Any-map⁺ (here p)  = here p
  Any-map⁺ (there p) = there (Any-map⁺ p)

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

    -- stdlib
    Any-++⁺ˡ : ∀ {xs ys} → Any P xs → Any P (xs ++ ys)
    Any-++⁺ˡ (here p)  = here p
    Any-++⁺ˡ (there p) = there (Any-++⁺ˡ p)
    
    -- stdlib
    Any-++⁺ʳ : ∀ xs {ys} → Any P ys → Any P (xs ++ ys)
    Any-++⁺ʳ []       p = p
    Any-++⁺ʳ (x ∷ xs) p = there (Any-++⁺ʳ xs p)

    -- stdlib
    Any-++⁻ : ∀ xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
    Any-++⁻ []       p         = inj₂ p
    Any-++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
    Any-++⁻ (x ∷ xs) (there p) = mapₛ there id (Any-++⁻ xs p)

    -- stdlib
    Any-concat⁺ : ∀ {xss} → Any (Any P) xss → Any P (concat xss)
    Any-concat⁺ (here p)           = Any-++⁺ˡ p
    Any-concat⁺ (there {x = xs} p) = Any-++⁺ʳ xs (Any-concat⁺ p)
  
    -- stdlib
    Any-tabulate⁺ : ∀ {n} {f : Fin n → A} i → P (f i) → Any P (tabulate f)
    Any-tabulate⁺ fzero    Pf₀  = here Pf₀
    Any-tabulate⁺ (fsuc i) Pf₁₊ᵢ = there (Any-tabulate⁺ i Pf₁₊ᵢ)

    -- stdlib
    Any-tabulate⁻ : ∀ {n} {f : Fin n → A} → Any P (tabulate f) → ∃ λ i → P (f i)
    Any-tabulate⁻ {n = zero}  ()
    Any-tabulate⁻ {n = suc n} (here Pf₀) = fzero , Pf₀
    Any-tabulate⁻ {n = suc n} (there Pfᵢ₊₁) = mapₚ fsuc id (Any-tabulate⁻ Pfᵢ₊₁)
  
    -- stdlib
    Any-applyUpTo⁺ : ∀ f {i n} → P (f i) → i < n → Any P (applyUpTo f n)
    Any-applyUpTo⁺ _ Pf₀ (s≤s z≤n)       = here Pf₀
    Any-applyUpTo⁺ f Pfᵢ  (s≤s (s≤s i<n)) = there (Any-applyUpTo⁺ (f ∘ suc) Pfᵢ (s≤s i<n))

    -- stdlib
    Any-applyUpTo⁻ : ∀ f {n} → Any P (applyUpTo f n) → ∃ λ i → i < n × P (f i)
    Any-applyUpTo⁻ f {zero}  ()
    Any-applyUpTo⁻ f {suc n} (here Pf₀) = zero , s≤s z≤n , Pf₀
    Any-applyUpTo⁻ f {suc n} (there Pfᵢ) with Any-applyUpTo⁻ (f ∘ suc) Pfᵢ
    ... | i , i<n , Pf₁₊ᵢ = suc i , s≤s i<n , Pf₁₊ᵢ


    Any-applyBetween⁺ : ∀ f {s e i} → s ≤ i → i < e → P (f i) → Any P (applyBetween f s e)
    Any-applyBetween⁺ f z≤n       (s≤s i<e) Pf₀ = Any-applyUpTo⁺ f Pf₀ (s≤s i<e)
    Any-applyBetween⁺ f (s≤s s≤i) (s≤s i<e) Pfᵢ = Any-applyBetween⁺ (f ∘ suc) s≤i i<e Pfᵢ

    Any-applyBetween⁻ : ∀ f s e → Any P (applyBetween f s e) → ∃ λ i → s ≤ i × i < e × P (f i)
    Any-applyBetween⁻ f zero    _       pxs = mapₚ id (z≤n ,_) (Any-applyUpTo⁻ f pxs)
    Any-applyBetween⁻ f (suc s) zero    ()
    Any-applyBetween⁻ f (suc s) (suc e) pxs with Any-applyBetween⁻ (f ∘ suc) s e pxs
    ... | i , s≤i , i<e , Pfᵢ = suc i , s≤s s≤i , s≤s i<e , Pfᵢ







  module _ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} where
  
    Any₂-++⁺ˡ : ∀ {ws xs ys zs} → Any₂ _~_ ws xs → Any₂ _~_ (ws ++ ys) (xs ++ zs)
    Any₂-++⁺ˡ (here x~y)    = here x~y
    Any₂-++⁺ˡ (there ws~xs) = there (Any₂-++⁺ˡ ws~xs)

    Any₂-++⁺ʳ : ∀ {ws xs ys zs} → length ws ≡ length xs → Any₂ _~_ ys zs → Any₂ _~_ (ws ++ ys) (xs ++ zs)
    Any₂-++⁺ʳ {[]}     {[]}     refl          ys~zs = ys~zs
    Any₂-++⁺ʳ {[]}     {_ ∷ _}  ()
    Any₂-++⁺ʳ {_ ∷ _}  {[]}     ()
    Any₂-++⁺ʳ {_ ∷ ws} {_ ∷ xs} 1+|ws|≡1+|xs| ys~zs = there (Any₂-++⁺ʳ {ws} {xs} (suc-injective 1+|ws|≡1+|xs|) ys~zs)
