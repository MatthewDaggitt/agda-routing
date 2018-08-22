open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; ≤-pred) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≰⇒>; <⇒≢; <⇒≯; ≤-refl; ≤-trans; 1+n≰n; _<?_; ≰⇒≥)
open import Data.Fin using (Fin; _<_; _≤?_; toℕ; fromℕ≤) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cmp; ≤-antisym; ≤-total; toℕ-fromℕ≤) renaming (_≟_ to _≟𝔽_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Function using (_∘_)
open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Setoid; DecSetoid; Decidable; Total; Reflexive; Symmetric; Antisymmetric; Transitive; _Respects_; IsEquivalence; IsDecEquivalence; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂) renaming (setoid to ≡-setoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (setoid to listSetoid)
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Relation.Nullary.Negation using (¬?)

open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)
open import RoutingLib.Data.VertexPath.NonEmpty
open import RoutingLib.Data.VertexPath.NonEmpty.Relation.Equality

module RoutingLib.Data.VertexPath.NonEmpty.Properties where

  abstract

  ----------------------
  -- Membership

    _∉?_ : Decidable _∉_
    k ∉? [ i ] with k ≟ℕ i
    ... | yes k≡i = no λ {(notThere k≢i) → k≢i k≡i}
    ... | no  k≢i = yes (notThere k≢i)
    k ∉? (i ∷ p ∣ _) with k ≟ℕ i | k ∉? p
    ... | yes k≡i | _       = no  λ{(notHere k≢i _) → k≢i k≡i }
    ... | _       | no  i∈p = no  λ{(notHere _ i∉p) → i∈p i∉p}
    ... | no  k≢i | yes i∉p = yes (notHere k≢i i∉p)

    _∈?_ : Decidable _∈_
    k ∈? p = ¬? (k ∉? p)
    
    ∉-resp-≈ₚ : ∀ {k} → (k ∉_) Respects _≈ₚ_
    ∉-resp-≈ₚ [ refl ]      (notThere k≢i)    = notThere k≢i
    ∉-resp-≈ₚ (refl ∷ p≈ₚq) (notHere k≢i k∉p) = notHere k≢i (∉-resp-≈ₚ p≈ₚq k∉p)

    --------------------
    -- Operations

    length-cong : ∀ {p q : Pathⁿᵗ} → p ≈ₚ q → length p ≡ length q
    length-cong [ _ ]       = refl
    length-cong (_ ∷ p≈ₚq) = cong suc (length-cong p≈ₚq)


    ------------------
    -- Arcs

    arc-toFromℕ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) → (toℕ (fromℕ≤ i<n) , toℕ (fromℕ≤ j<n)) ≡ (i , j)
    arc-toFromℕ i<n j<n = cong₂ _,_ (toℕ-fromℕ≤ i<n) (toℕ-fromℕ≤ j<n)
