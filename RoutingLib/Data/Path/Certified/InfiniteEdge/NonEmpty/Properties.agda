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

open import RoutingLib.Data.Path.EdgePath.NonEmpty
open import RoutingLib.Data.Path.EdgePath.NonEmpty.Relation.Equality

module RoutingLib.Data.Path.EdgePath.NonEmpty.Properties where

  abstract

    ----------------------
    -- Linking

    _⇿?_ : Decidable _⇿_
    (i , j) ⇿? [] with i ≟ℕ j
    ... | yes i≡j = no  λ{(start i≢j) → i≢j i≡j}
    ... | no  i≢j = yes (start i≢j)
    (i , j) ⇿? ((k , l) ∷ p ∣ e⇿p ∣ e∉p) with i ≟ℕ j | j ≟ℕ k
    ... | yes i≡j | _        = no λ{(continue i≢j) → i≢j i≡j}
    ... | no  _   | no  j≢k  = no λ{(continue _) → j≢k refl}
    ... | no  i≢j | yes refl = yes (continue i≢j)

    ⇿-resp-≈ₚ : ∀ {e : ℕ × ℕ} → (e ⇿_) Respects _≈ₚ_
    ⇿-resp-≈ₚ []           (start i≢j)    = start i≢j
    ⇿-resp-≈ₚ (refl ∷ p≈ₚq) (continue i≢j) = continue i≢j

    ij⇿p⇒i≢j : ∀ {i j : ℕ} {p} → (i , j) ⇿ p → i ≢ j
    ij⇿p⇒i≢j (start    i≢j) = i≢j
    ij⇿p⇒i≢j (continue i≢j) = i≢j

  ----------------------
  -- Membership

    _∉?_ : Decidable _∉_
    k ∉? [] = yes notThere
    k ∉? ((i , j) ∷ p ∣ _ ∣ _) with k ≟ℕ i | k ≟ℕ j | k ∉? p
    ... | yes k≡i | _       | _       = no  λ{(notHere k≢i _ _) → k≢i k≡i }
    ... | _       | yes k≡j | _       = no  λ{(notHere _ k≢j _) → k≢j k≡j }
    ... | _       | _       | no  i∈p = no  λ{(notHere _ _ i∉p) → i∈p i∉p}
    ... | no  k≢i | no  k≢j | yes i∉p = yes (notHere k≢i k≢j i∉p)

    _∈?_ : Decidable _∈_
    k ∈? p = ¬? (k ∉? p)

    ∉-resp-≈ₚ : ∀ {k} → (k ∉_) Respects _≈ₚ_
    ∉-resp-≈ₚ []            notThere             = notThere
    ∉-resp-≈ₚ (refl ∷ p≈ₚq) (notHere k≢i k≢j k∉p) = notHere k≢i k≢j (∉-resp-≈ₚ p≈ₚq k∉p)

    --------------------
    -- Operations

    length-cong : ∀ {p q} → p ≈ₚ q → length p ≡ length q
    length-cong []         = refl
    length-cong (_ ∷ p≈ₚq) = cong suc (length-cong p≈ₚq)


    ------------------
    -- Arcs

    arc-toFromℕ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) → (toℕ (fromℕ≤ i<n) , toℕ (fromℕ≤ j<n)) ≡ (i , j)
    arc-toFromℕ i<n j<n = cong₂ _,_ (toℕ-fromℕ≤ i<n) (toℕ-fromℕ≤ j<n)
