open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Setoid; DecSetoid; Decidable; Total; Reflexive; Symmetric; Antisymmetric; Transitive; _Respects_; IsEquivalence; IsDecEquivalence; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂) renaming (setoid to ≡-setoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (setoid to listSetoid)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; ≤-pred) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≰⇒>; <⇒≢; <⇒≯; ≤-refl; ≤-trans; 1+n≰n; _<?_; ≰⇒≥)
open import Data.Fin using (Fin; _<_; _≤?_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cmp; ≤-antisym; ≤-total) renaming (_≟_ to _≟𝔽_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Function using (_∘_)
open import Relation.Nullary.Negation using (¬?)

open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)
open import RoutingLib.Data.SimplePath.NonEmpty
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality

module RoutingLib.Data.SimplePath.NonEmpty.Properties {n} where

  abstract
  
    ----------------------
    -- Linking

    _⇿?_ : Decidable (_⇿_ {n})
    (i , j) ⇿? [] with i ≟𝔽 j
    ... | yes i≡j = no  λ{(start i≢j) → i≢j i≡j}
    ... | no  i≢j = yes (start i≢j)
    (i , j) ⇿? ((k , l) ∷ p ∣ e⇿p ∣ e∉p) with i ≟𝔽 j | j ≟𝔽 k
    ... | yes i≡j | _        = no λ{(continue i≢j) → i≢j i≡j}
    ... | no  _   | no  j≢k  = no λ{(continue _) → j≢k refl}
    ... | no  i≢j | yes refl = yes (continue i≢j)

    ⇿-resp-≈ₚ : ∀ {e : Fin n × Fin n} → (e ⇿_) Respects _≈ₚ_
    ⇿-resp-≈ₚ []           (start i≢j)    = start i≢j
    ⇿-resp-≈ₚ (refl ∷ p≈ₚq) (continue i≢j) = continue i≢j

    ij⇿p⇒i≢j : ∀ {n} {i j : Fin n} {p} → (i , j) ⇿ p → i ≢ j
    ij⇿p⇒i≢j (start    i≢j) = i≢j
    ij⇿p⇒i≢j (continue i≢j) = i≢j

  ----------------------
  -- Membership
  
    _∉?_ : Decidable (_∉_ {n})
    k ∉? [] = yes notThere
    k ∉? ((i , j) ∷ p ∣ _ ∣ _) with k ≟𝔽 i | k ≟𝔽 j | k ∉? p
    ... | yes k≡i | _       | _       = no  λ{(notHere k≢i _ _) → k≢i k≡i }
    ... | _       | yes k≡j | _       = no  λ{(notHere _ k≢j _) → k≢j k≡j }
    ... | _       | _       | no  i∈p = no  λ{(notHere _ _ i∉p) → i∈p i∉p}
    ... | no  k≢i | no  k≢j | yes i∉p = yes (notHere k≢i k≢j i∉p)

    _∈?_ : Decidable (_∈_ {n})
    k ∈? p = ¬? (k ∉? p)
    
    ∉-resp-≈ₚ : ∀ {k : Fin n} → (k ∉_) Respects _≈ₚ_
    ∉-resp-≈ₚ []            notThere             = notThere
    ∉-resp-≈ₚ (refl ∷ p≈ₚq) (notHere k≢i k≢j k∉p) = notHere k≢i k≢j (∉-resp-≈ₚ p≈ₚq k∉p)

    --------------------
    -- Operations

    length-cong : ∀ {p q : SimplePathⁿᵗ n} → p ≈ₚ q → length p ≡ length q
    length-cong []        = refl
    length-cong (_ ∷ p≈ₚq) = cong suc (length-cong p≈ₚq)


    ∉-lookup : ∀ {p : SimplePathⁿᵗ n} (p⁺ : NonEmpty p) →
               ∀ {i} → i ∉ p → ∀ k → lookupᵥ p⁺ k ≢ i
    ∉-lookup (nonEmpty .(_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) fzero = x ∘ sym
    ∉-lookup (nonEmpty .(_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (fsuc fzero) = x₁ ∘ sym
    ∉-lookup (nonEmpty .(_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (fsuc (fsuc ()))
    ∉-lookup (nonEmpty .(_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) fzero = x ∘ sym
    ∉-lookup (nonEmpty .(_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (fsuc fzero) = x₁ ∘ sym
    ∉-lookup (nonEmpty .(_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (fsuc (fsuc k)) =
      ∉-lookup (nonEmpty e p e⇿p₁ e∉p₁) i∉p (fsuc k)

    ∉-lookup₂ : ∀ {p : SimplePathⁿᵗ n} (p⁺ : NonEmpty p) →
                ∀ {i j} → (i , j) ⇿ p → ∀ k → lookupᵥ p⁺ (fsuc k) ≢ j
    ∉-lookup₂ (nonEmpty (j , l) p e⇿p e∉p) {i} {.j} (continue x) fzero    = ij⇿p⇒i≢j e⇿p ∘ sym
    ∉-lookup₂ (nonEmpty (j , l) [] e⇿p e∉p) {i} {.j} (continue x) (fsuc ())
    ∉-lookup₂ (nonEmpty (j , l) (.(_ , _) ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p (notHere x₁ x₂ e∉p)) {i} {.j} (continue x) (fsuc fzero) = x₂ ∘ sym
    ∉-lookup₂ (nonEmpty (j , l) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) {i} {.j} (continue x) (fsuc (fsuc k)) = 
      ∉-lookup (nonEmpty e p e⇿p₁ e∉p₁) e∉p (fsuc (fsuc k))
    
    lookup! : ∀ {p : SimplePathⁿᵗ n} (p⁺ : NonEmpty p) → ∀ k l → k ≢ l → lookupᵥ p⁺ k ≢ lookupᵥ p⁺ l
    lookup! (nonEmpty e p e⇿p e∉p)               fzero           fzero           0≢0 = contradiction refl 0≢0
    lookup! (nonEmpty e p e⇿p e∉p)               fzero           (fsuc fzero)    _   = ij⇿p⇒i≢j e⇿p
    lookup! (nonEmpty e [] e⇿p e∉p)              fzero           (fsuc (fsuc ()))
    lookup! (nonEmpty e p e⇿p e∉p)               (fsuc fzero)    fzero           _   = ij⇿p⇒i≢j e⇿p ∘ sym
    lookup! (nonEmpty e [] e⇿p e∉p)              (fsuc (fsuc ())) _      
    lookup! (nonEmpty e p e⇿p e∉p)               (fsuc fzero)    (fsuc fzero)    1≢1 = contradiction refl 1≢1
    lookup! (nonEmpty e [] e⇿p e∉p)              (fsuc fzero)    (fsuc (fsuc ()))
    lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) fzero           (fsuc (fsuc l)) _   =
      (∉-lookup (nonEmpty f p a b) e∉p (fsuc l)) ∘ sym
    lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (fsuc (fsuc k)) fzero           _   =
      (∉-lookup (nonEmpty f p a b) e∉p (fsuc k))
    lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (fsuc fzero)    (fsuc (fsuc l)) _   =
      ∉-lookup₂ (nonEmpty f p a b) e⇿p l ∘ sym
    lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (fsuc (fsuc k)) (fsuc fzero)    _   =
      ∉-lookup₂ (nonEmpty f p a b) e⇿p k
    lookup! (nonEmpty e (_ ∷ _ ∣ _ ∣ _) e⇿p e∉p) (fsuc (fsuc k)) (fsuc (fsuc l)) k≢l =
      lookup! (nonEmpty _ _ _ _) (fsuc k) (fsuc l) (k≢l ∘ cong fsuc)

    |p|<n : ∀ {p : SimplePathⁿᵗ n} → NonEmpty p → length p <ℕ n
    |p|<n q@(nonEmpty e p e⇿p e∉p) with suc (length p) <? n
    ... | yes |q|<n = |q|<n
    ... | no  |q|≮n with pigeonhole (≰⇒> |q|≮n) (lookupᵥ q)
    ...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookup! q i j i≢j)

    test : ∀ {x y} → x <ℕ y → x ≤ℕ suc y
    test (s≤s z≤n)       = z≤n
    test (s≤s (s≤s x<y)) = s≤s (test (s≤s x<y))
    
    |p|≤1+n : ∀ (p : SimplePathⁿᵗ n) → length p ≤ℕ suc n
    |p|≤1+n []                   = z≤n
    |p|≤1+n (e ∷ p ∣ e⇿p ∣ e∉p) = test (|p|<n (nonEmpty _ _ e⇿p e∉p))
