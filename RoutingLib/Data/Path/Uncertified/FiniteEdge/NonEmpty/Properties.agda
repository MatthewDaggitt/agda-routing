open import Level using () renaming (zero to 0ℓ)
open import Data.List.Any using (any)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; ≤-pred) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≰⇒>; <⇒≢; <⇒≯; ≤-refl; ≤-trans; 1+n≰n; _<?_; ≰⇒≥)
open import Data.Fin using (Fin; _<_; _≤?_; _≟_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (<-cmp; ≤-antisym; ≤-total) renaming (_≟_ to _≟𝔽_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; setoid; isEquivalence)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Nat.Properties using (<⇒≤suc)
open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)
import RoutingLib.Relation.Binary.NonStrictToStrict.DecTotalOrder as ToStrict

open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty

module RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty.Properties where

----------------------------------------------------------------------------
-- Edges

_≟ₑ_ : ∀ {n} → Decidable {A = Edge n} _≡_
_≟ₑ_ = _≟𝔽_ ×-≟ _≟𝔽_

𝕍ₛ : ℕ → Setoid _ _
𝕍ₛ n = setoid (Vertex n)

𝔼ₛ : ℕ → Setoid _ _
𝔼ₛ n = setoid (Edge n)

----------------------------------------------------------------------------
-- Linking

_⇿?_ : ∀ {n} → Decidable (_⇿_ {n})
(i , j) ⇿? [] with i ≟𝔽 j
... | yes i≡j = no  λ{(start i≢j) → i≢j i≡j}
... | no  i≢j = yes (start i≢j)
(i , j) ⇿? ((k , l) ∷ p) with i ≟𝔽 j | j ≟𝔽 k
... | yes i≡j | _        = no λ{(continue i≢j) → i≢j i≡j}
... | no  _   | no  j≢k  = no λ{(continue _) → j≢k refl}
... | no  i≢j | yes refl = yes (continue i≢j)

⇿-resp-≈ₚ : ∀ {n} {e : Edge n} → (e ⇿_) Respects _≈ₚ_
⇿-resp-≈ₚ refl e⇿p = e⇿p

ij⇿p⇒i≢j : ∀ {n} {i j : Vertex n} {p} → (i , j) ⇿ p → i ≢ j
ij⇿p⇒i≢j (start    i≢j) = i≢j
ij⇿p⇒i≢j (continue i≢j) = i≢j

----------------------------------------------------------------------------
-- Membership

_∈ₑ?_ : ∀ {n} → Decidable (_∈ₑ_ {n})
k ∈ₑ? (i , j) with k ≟ i | k ≟ j
... | yes refl | _        = yes left
... | _        | yes refl = yes right
... | no  k≢i  | no  k≢j  = no λ
  { left  → k≢i refl
  ; right → k≢j refl
  }

_∈?_ : ∀ {n} → Decidable (_∈_ {n})
k ∈? p = any (k ∈ₑ?_) p

∉-resp-≈ₚ : ∀ {n} {k : Fin n} → (k ∉_) Respects _≡_
∉-resp-≈ₚ refl k∉p = k∉p

----------------------------------------------------------------------------
-- Equality

p≉i∷p : ∀ {n e} {p : Pathⁿᵗ n} → ¬ (p ≈ₚ e ∷ p)
p≉i∷p {p}    ()

_≟ₚ_ : ∀ {n} → Decidable (_≈ₚ_ {n})
[]      ≟ₚ []      = yes refl
[]      ≟ₚ (k ∷ q) = no λ()
(i ∷ p) ≟ₚ []      = no λ()
(i ∷ p) ≟ₚ (k ∷ q) with i ≟ₑ k | p ≟ₚ q
... | no  i≢k  | _        = no (λ{refl → i≢k refl})
... | _        | no  p≢q  = no (λ{refl → p≢q refl})
... | yes refl | yes refl = yes refl

module _ (n : ℕ) where

  ≡ₚ-isDecEquivalence : IsDecEquivalence (_≈ₚ_ {n})
  ≡ₚ-isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_           = _≟ₚ_
    }

  ℙₛ : Setoid 0ℓ 0ℓ
  ℙₛ = setoid (Pathⁿᵗ n)
  
  ℙₛ? : DecSetoid 0ℓ 0ℓ
  ℙₛ? = record { isDecEquivalence = ≡ₚ-isDecEquivalence }

----------------------------------------------------------------------------
-- Lexicographic order

module _ {n : ℕ} where

  ≤ₗₑₓ-refl : Reflexive (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-refl {[]}    = stop
  ≤ₗₑₓ-refl {i ∷ p} = step refl refl ≤ₗₑₓ-refl
  
  ≤ₗₑₓ-reflexive : _≡_ ⇒ (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-reflexive refl = ≤ₗₑₓ-refl

  ≤ₗₑₓ-total : Total (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-total p [] = inj₂ stop
  ≤ₗₑₓ-total [] q = inj₁ stop
  ≤ₗₑₓ-total ((i , j) ∷ p) ((l , k) ∷ q) with <-cmp i l
  ... | tri< i<l _ _ = inj₁ (here₁ i<l)
  ... | tri> _ _ l<i = inj₂ (here₁ l<i)
  ... | tri≈ _ i≡l _ with <-cmp j k
  ...   | tri< j<k _ _ = inj₁ (here₂ i≡l j<k)
  ...   | tri> _ _ j<k = inj₂ (here₂ (sym i≡l) j<k)
  ...   | tri≈ _ j≡k _ with ≤ₗₑₓ-total p q
  ...     | inj₁ p≤q = inj₁ (step i≡l j≡k p≤q)
  ...     | inj₂ q≤p = inj₂ (step (sym i≡l) (sym j≡k) q≤p)

  ≤ₗₑₓ-trans : Transitive (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-trans stop                  _                     = stop
  ≤ₗₑₓ-trans (here₁ i<j)           (here₁ j<k)           = here₁ (<-trans i<j j<k)
  ≤ₗₑₓ-trans (here₁ i<j)           (here₂ refl j<k)      = here₁ i<j
  ≤ₗₑₓ-trans (here₁ i<j)           (step  refl refl q≤r) = here₁ i<j
  ≤ₗₑₓ-trans (here₂ refl i<j)      (here₁ j<k)           = here₁ j<k
  ≤ₗₑₓ-trans (here₂ refl i<j)      (here₂ refl j<k)      = here₂ refl (<-trans i<j j<k)
  ≤ₗₑₓ-trans (here₂ refl i<j)      (step  refl refl q≤r) = here₂ refl i<j
  ≤ₗₑₓ-trans (step  refl refl p≤q) (here₁ j<k)           = here₁ j<k
  ≤ₗₑₓ-trans (step  refl refl p≤q) (here₂ refl j<k)      = here₂ refl j<k
  ≤ₗₑₓ-trans (step  refl refl p≤q) (step  refl refl q≤r) = step refl refl (≤ₗₑₓ-trans p≤q q≤r)

  ≤ₗₑₓ-antisym : Antisymmetric _≈ₚ_ (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-antisym stop                  stop                  = refl
  ≤ₗₑₓ-antisym (here₁ i<j)           (here₁ j<i)           = contradiction i<j (<⇒≯ j<i)
  ≤ₗₑₓ-antisym (here₁ i<j)           (here₂ refl j<i)      = contradiction i<j 1+n≰n
  ≤ₗₑₓ-antisym (here₁ i<j)           (step  refl refl p≤q) = contradiction i<j 1+n≰n
  ≤ₗₑₓ-antisym (here₂ refl i<j)      (here₁ j<i)           = contradiction j<i 1+n≰n
  ≤ₗₑₓ-antisym (here₂ refl i<j)      (here₂ refl j<i)      = contradiction i<j (<⇒≯ j<i)
  ≤ₗₑₓ-antisym (here₂ refl i<j)      (step  refl refl p≤q) = contradiction i<j 1+n≰n
  ≤ₗₑₓ-antisym (step  refl refl i<j) (here₁ j<i)           = contradiction j<i 1+n≰n
  ≤ₗₑₓ-antisym (step  refl refl _)   (here₂ _ j<i)         = contradiction j<i 1+n≰n
  ≤ₗₑₓ-antisym (step  refl refl p≤q) (step refl refl q≤p)  = cong (_ ∷_) (≤ₗₑₓ-antisym p≤q q≤p)
  
  _≤ₗₑₓ?_ : Decidable (_≤ₗₑₓ_ {n})
  [] ≤ₗₑₓ? _ = yes stop
  (i ∷ p) ≤ₗₑₓ? []          = no λ()
  ((i , j) ∷ p) ≤ₗₑₓ? ((k , l) ∷ q) with <-cmp i k | <-cmp j l | p ≤ₗₑₓ? q
  ... | tri< i<k _   _ | _              | _       = yes (here₁ i<k)
  ... | tri> i≮k i≢k _ | _              | _       = no λ
    { (here₁ i<k)     → i≮k i<k
    ; (here₂ i≡k _)   → i≢k i≡k
    ; (step  i≡k _ _) → i≢k i≡k
    }
  ... | tri≈ _   i≡k _ | tri< j<l _   _ | _       = yes (here₂ i≡k j<l)
  ... | tri≈ i≮k _   _ | tri> j≮l j≢l _ | _       = no λ
    { (here₁ i<k)     → i≮k i<k
    ; (here₂ _ j<l)   → j≮l j<l
    ; (step  _ j≡l _) → j≢l j≡l
    }
  ... | tri≈ i≮k _   _ | tri≈ j≮l _ _   | no  p≰q = no λ
    { (here₁ i<k)     → i≮k i<k
    ; (here₂ _ j<l)   → j≮l j<l
    ; (step  _ _ p≤q) → p≰q p≤q
    }
  ... | tri≈ _   i≡k _ | tri≈ _ j≡l _   | yes p≤q = yes (step i≡k j≡l p≤q)


module _ (n : ℕ) where

  ≤ₗₑₓ-decTotalOrder : DecTotalOrder _ _ _
  ≤ₗₑₓ-decTotalOrder = record
    { isDecTotalOrder = record
      { isTotalOrder = record
        { isPartialOrder = record
          { isPreorder = record
            { isEquivalence = isEquivalence {A = Pathⁿᵗ n} 
            ; reflexive     = ≤ₗₑₓ-reflexive
            ; trans         = ≤ₗₑₓ-trans
            }
          ; antisym    = ≤ₗₑₓ-antisym
          }
        ; total        = ≤ₗₑₓ-total
        }
      ; _≟_          = _≟ₚ_
      ; _≤?_         = _≤ₗₑₓ?_
      }
    }

module _ {n : ℕ} where

  open ToStrict (≤ₗₑₓ-decTotalOrder n) public
    using ()
    renaming
    ( <-trans   to <ₗₑₓ-trans
    ; <-asym    to <ₗₑₓ-asym
    ; <-irrefl  to <ₗₑₓ-irrefl
    ; <-respˡ-≈ to <ₗₑₓ-respˡ-≈ₚ
    ; <-respʳ-≈ to <ₗₑₓ-respʳ-≈ₚ
    ; <-cmp     to <ₗₑₓ-cmp
    )

  p≮ₗₑₓ[] : ∀ {p : Pathⁿᵗ n} → ¬ (p <ₗₑₓ [])
  p≮ₗₑₓ[] {[]}    (_ , []≉[]) = []≉[] refl
  p≮ₗₑₓ[] {e ∷ p} (() , _)

{-

----------------------------------------------------------------------------
-- lookup

∉-lookup : ∀ {n} {p : Pathⁿᵗ n} (p⁺ : NonEmpty p) →
           ∀ {i} → i ∉ p → ∀ k → lookupᵥ p⁺ k ≢ i
∉-lookup (nonEmpty (_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) fzero = x ∘ sym
∉-lookup (nonEmpty (_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (fsuc fzero) = x₁ ∘ sym
∉-lookup (nonEmpty (_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (fsuc (fsuc ()))
∉-lookup (nonEmpty (_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) fzero = x ∘ sym
∉-lookup (nonEmpty (_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (fsuc fzero) = x₁ ∘ sym
∉-lookup (nonEmpty (_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (fsuc (fsuc k)) =
  ∉-lookup (nonEmpty e p e⇿p₁ e∉p₁) i∉p (fsuc k)

∉-lookup₂ : ∀ {n} {p : Pathⁿᵗ n} (p⁺ : NonEmpty p) →
            ∀ {i j} → (i , j) ⇿ p → ∀ k → lookupᵥ p⁺ (fsuc k) ≢ j
∉-lookup₂ (nonEmpty (j , l) p  e⇿p e∉p) (continue x) fzero    = ij⇿p⇒i≢j e⇿p ∘ sym
∉-lookup₂ (nonEmpty (j , l) [] e⇿p e∉p) (continue x) (fsuc ())
∉-lookup₂ (nonEmpty (j , l) ((_ , _) ∷ p ∣ _ ∣ _) _ (notHere _ j≢l _)) (continue _) (fsuc fzero) = j≢l ∘ sym
∉-lookup₂ (nonEmpty (j , l) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) _ e∉p) (continue x) (fsuc (fsuc k)) =
  ∉-lookup (nonEmpty e p e⇿p₁ e∉p₁) e∉p (fsuc (fsuc k))

lookup! : ∀ {n} {p : Pathⁿᵗ n} (p⁺ : NonEmpty p) → ∀ k l → k ≢ l → lookupᵥ p⁺ k ≢ lookupᵥ p⁺ l
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

----------------------------------------------------------------------------
-- length

length-cong : ∀ {n} {p q : Pathⁿᵗ n} → p ≈ₚ q → length p ≡ length q
length-cong []        = refl
length-cong (_ ∷ p≈ₚq) = cong suc (length-cong p≈ₚq)

|p|<n : ∀ {n} {p : Pathⁿᵗ n} → NonEmpty p → length p <ℕ n
|p|<n {n} q@(nonEmpty e p e⇿p e∉p) with suc (length p) <? n
... | yes |q|<n = |q|<n
... | no  |q|≮n with pigeonhole (≰⇒> |q|≮n) (lookupᵥ q)
...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookup! q i j i≢j)

|p|≤1+n : ∀ {n} (p : Pathⁿᵗ n) → length p ≤ℕ suc n
|p|≤1+n []                  = z≤n
|p|≤1+n (e ∷ p ∣ e⇿p ∣ e∉p) = <⇒≤suc (|p|<n (nonEmpty _ _ e⇿p e∉p))
-}
