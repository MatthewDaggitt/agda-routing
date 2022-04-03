open import Level using () renaming (zero to 0ℓ)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; ≤-pred) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≰⇒>; <⇒≢; <⇒≯; ≤-refl; ≤-trans; 1+n≰n; _<?_; ≰⇒≥; <⇒≤)
open import Data.Fin using (Fin; _<_; _≤?_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (<-cmp; ≤-antisym; ≤-total; pigeonhole) renaming (_≟_ to _≟𝔽_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Function using (_∘_)
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; setoid)
open import Relation.Nullary.Negation using (¬?)

open import RoutingLib.Data.Nat.Properties using (<⇒≤suc)
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.DecTotalOrder as ToStrict

open import RoutingLib.Routing.Basics.Path.Certified

module RoutingLib.Routing.Basics.Path.Certified.Properties where

----------------------------------------------------------------------------
-- Edges

_≟ₑ_ : ∀ {n} → Decidable {A = Edge n} _≡_
_≟ₑ_ = ≡-dec _≟𝔽_ _≟𝔽_

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
(i , j) ⇿? ((k , l) ∷ p ∣ e⇿p ∣ e∉p) with i ≟𝔽 j | j ≟𝔽 k
... | yes i≡j | _        = no λ{(continue i≢j) → i≢j i≡j}
... | no  _   | no  j≢k  = no λ{(continue _) → j≢k refl}
... | no  i≢j | yes refl = yes (continue i≢j)

⇿-resp-≈ₚ : ∀ {n} {e : Edge n} → (e ⇿_) Respects _≈ₚ_
⇿-resp-≈ₚ []           (start i≢j)    = start i≢j
⇿-resp-≈ₚ (refl ∷ p≈ₚq) (continue i≢j) = continue i≢j

⇿-sub : ∀ {n i j k} {p : Path n} → (i , j) ⇿ p → k ≢ j → (k , j) ⇿ p
⇿-sub (start _)    k≢j = start k≢j
⇿-sub (continue _) k≢j = continue k≢j

ij⇿p⇒i≢j : ∀ {n} {i j : Vertex n} {p} → (i , j) ⇿ p → i ≢ j
ij⇿p⇒i≢j (start    i≢j) = i≢j
ij⇿p⇒i≢j (continue i≢j) = i≢j

----------------------------------------------------------------------------
-- Membership

_∉ₚ?_ : ∀ {n} → Decidable (_∉ₚ_ {n})
k ∉ₚ? [] = yes notThere
k ∉ₚ? ((i , j) ∷ p ∣ _ ∣ _) with k ≟𝔽 i | k ≟𝔽 j | k ∉ₚ? p
... | yes k≡i | _       | _       = no  λ{(notHere k≢i _ _) → k≢i k≡i }
... | _       | yes k≡j | _       = no  λ{(notHere _ k≢j _) → k≢j k≡j }
... | _       | _       | no  i∈p = no  λ{(notHere _ _ i∉p) → i∈p i∉p}
... | no  k≢i | no  k≢j | yes i∉p = yes (notHere k≢i k≢j i∉p)

_∈ₚ?_ : ∀ {n} → Decidable (_∈ₚ_ {n})
k ∈ₚ? p = ¬? (k ∉ₚ? p)

∉ₚ-resp-≈ₚ : ∀ {n} {k : Fin n} → (k ∉ₚ_) Respects _≈ₚ_
∉ₚ-resp-≈ₚ []            notThere             = notThere
∉ₚ-resp-≈ₚ (refl ∷ p≈ₚq) (notHere k≢i k≢j k∉p) = notHere k≢i k≢j (∉ₚ-resp-≈ₚ p≈ₚq k∉p)

----------------------------------------------------------------------------
-- Equality

p≉i∷p : ∀ {n e} {p : Path n} {e⇿p e∉p} → ¬ (p ≈ₚ e ∷ p ∣ e⇿p ∣ e∉p)
p≉i∷p {p = []}            ()
p≉i∷p {p = _ ∷ _ ∣ _ ∣ _} (_ ∷ p≈ₚi∷p) = p≉i∷p p≈ₚi∷p

-- Injectivity properties

module _ {n} {i j k l : Vertex n} {p q w x y z} where

  ∷ˡ-injective₁ : (i , j) ∷ p ∣ w ∣ x ≈ₚ (k , l) ∷ q ∣ y ∣ z → i ≡ k
  ∷ˡ-injective₁ (refl ∷ _) = refl

  ∷ˡ-injective₂ : (i , j) ∷ p ∣ w ∣ x ≈ₚ (k , l) ∷ q ∣ y ∣ z → j ≡ l
  ∷ˡ-injective₂ (refl ∷ _) = refl

  ∷ʳ-injective : (i , j) ∷ p ∣ w ∣ x ≈ₚ (k , l) ∷ q ∣ y ∣ z → p ≈ₚ q
  ∷ʳ-injective (_ ∷ p≈q) = p≈q

-- Relational properties

module _ {n : ℕ} where

  ≈ₚ-refl : Reflexive (_≈ₚ_ {n})
  ≈ₚ-refl {[]}            = []
  ≈ₚ-refl {_ ∷ _ ∣ _ ∣ _} = refl ∷ ≈ₚ-refl

  ≈ₚ-reflexive : _≡_ ⇒ (_≈ₚ_ {n})
  ≈ₚ-reflexive refl = ≈ₚ-refl

  ≈ₚ-sym : Symmetric (_≈ₚ_ {n})
  ≈ₚ-sym []           = []
  ≈ₚ-sym (refl ∷ p≈ₚq) = refl ∷ (≈ₚ-sym p≈ₚq)

  ≈ₚ-trans : Transitive (_≈ₚ_ {n})
  ≈ₚ-trans []            []           = []
  ≈ₚ-trans (refl ∷ p≈ₚq)  (refl ∷ q≈ₚr) = refl ∷ (≈ₚ-trans p≈ₚq q≈ₚr)

  _≟ₚ_ : Decidable (_≈ₚ_ {n})
  []              ≟ₚ []              = yes []
  []              ≟ₚ (k ∷ q ∣ _ ∣ _) = no λ()
  (i ∷ p ∣ _ ∣ _) ≟ₚ []              = no λ()
  (i ∷ p ∣ _ ∣ _) ≟ₚ (k ∷ q ∣ _ ∣ _) with i ≟ₑ k | p ≟ₚ q
  ... | no  i≢k | _       = no (λ{(i≡k ∷ _) → i≢k i≡k})
  ... | _       | no  p≢q = no (λ{(_ ∷ p≡q) → p≢q p≡q})
  ... | yes i≡k | yes p≡q = yes (i≡k ∷ p≡q)

module _ (n : ℕ) where

  ≈ₚ-isEquivalence : IsEquivalence (_≈ₚ_ {n})
  ≈ₚ-isEquivalence = record
    { refl  = ≈ₚ-refl
    ; sym   = ≈ₚ-sym
    ; trans = ≈ₚ-trans
    }

  ≈ₚ-isDecEquivalence : IsDecEquivalence (_≈ₚ_ {n})
  ≈ₚ-isDecEquivalence = record
    { isEquivalence = ≈ₚ-isEquivalence
    ; _≟_           = _≟ₚ_
    }

  ℙₛ : Setoid 0ℓ 0ℓ
  ℙₛ = record { isEquivalence = ≈ₚ-isEquivalence}

  ℙₛ? : DecSetoid 0ℓ 0ℓ
  ℙₛ? = record { isDecEquivalence = ≈ₚ-isDecEquivalence }



----------------------------------------------------------------------------
-- Lexicographic order

module _ {n : ℕ} where

  ≤ₗₑₓ-reflexive : _≈ₚ_ ⇒ (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-reflexive []         = stop
  ≤ₗₑₓ-reflexive (refl ∷ p≈q) = step refl refl (≤ₗₑₓ-reflexive p≈q)

  ≤ₗₑₓ-refl : Reflexive (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-refl {[]}            = stop
  ≤ₗₑₓ-refl {i ∷ p ∣ _ ∣ _} = step refl refl ≤ₗₑₓ-refl

  ≤ₗₑₓ-total : Total (_≤ₗₑₓ_ {n})
  ≤ₗₑₓ-total p [] = inj₂ stop
  ≤ₗₑₓ-total [] q = inj₁ stop
  ≤ₗₑₓ-total ((i , j) ∷ p ∣ e⇿p ∣ e∉p) ((l , k) ∷ q ∣ f⇿q ∣ f∉q) with <-cmp i l
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
  ≤ₗₑₓ-antisym stop                  stop                  = []
  ≤ₗₑₓ-antisym (here₁ i<j)           (here₁ j<i)           = contradiction i<j (<⇒≯ j<i)
  ≤ₗₑₓ-antisym (here₁ i<j)           (here₂ refl j<i)      = contradiction i<j 1+n≰n
  ≤ₗₑₓ-antisym (here₁ i<j)           (step  refl refl p≤q) = contradiction i<j 1+n≰n
  ≤ₗₑₓ-antisym (here₂ refl i<j)      (here₁ j<i)           = contradiction j<i 1+n≰n
  ≤ₗₑₓ-antisym (here₂ refl i<j)      (here₂ refl j<i)      = contradiction i<j (<⇒≯ j<i)
  ≤ₗₑₓ-antisym (here₂ refl i<j)      (step  refl refl p≤q) = contradiction i<j 1+n≰n
  ≤ₗₑₓ-antisym (step  refl refl i<j) (here₁ j<i)           = contradiction j<i 1+n≰n
  ≤ₗₑₓ-antisym (step  refl refl _)   (here₂ _ j<i)         = contradiction j<i 1+n≰n
  ≤ₗₑₓ-antisym (step  refl refl p≤q) (step refl refl q≤p)  = refl ∷ ≤ₗₑₓ-antisym p≤q q≤p

  _≤ₗₑₓ?_ : Decidable (_≤ₗₑₓ_ {n})
  [] ≤ₗₑₓ? _ = yes stop
  (i ∷ p ∣ _ ∣ _) ≤ₗₑₓ? []          = no λ()
  ((i , j) ∷ p ∣ _ ∣ _) ≤ₗₑₓ? ((k , l) ∷ q ∣ _ ∣ _) with <-cmp i k | <-cmp j l | p ≤ₗₑₓ? q
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
            { isEquivalence = ≈ₚ-isEquivalence n
            ; reflexive     = ≤ₗₑₓ-reflexive
            ; trans         = ≤ₗₑₓ-trans
            }
          ; antisym    = ≤ₗₑₓ-antisym
          }
        ; total          = ≤ₗₑₓ-total
        }
      ; _≟_          = _≟ₚ_
      ; _≤?_         = _≤ₗₑₓ?_
      }
    }

  open ToStrict ≤ₗₑₓ-decTotalOrder public
    using ()
    renaming
    ( _<_       to _<ₗₑₓ_
    ; <-trans   to <ₗₑₓ-trans
    ; <-asym    to <ₗₑₓ-asym
    ; <-irrefl  to <ₗₑₓ-irrefl
    ; <-respˡ-≈ to <ₗₑₓ-respˡ-≈ₚ
    ; <-respʳ-≈ to <ₗₑₓ-respʳ-≈ₚ
    ; <-cmp     to <ₗₑₓ-cmp
    )

  p≮ₗₑₓ[] : ∀ {p} → ¬ (p <ₗₑₓ [])
  p≮ₗₑₓ[] {[]}                (_ , []≉[]) = []≉[] []
  p≮ₗₑₓ[] {e ∷ p ∣ e⇿p ∣ e∉p} (() , _)

----------------------------------------------------------------------------
-- lookup

∉ₚ-lookup : ∀ {n} {p : Path n} (p⁺ : NonEmpty p) →
           ∀ {i} → i ∉ₚ p → ∀ k → lookupᵥ p⁺ k ≢ i
∉ₚ-lookup (nonEmpty (_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) fzero = x ∘ sym
∉ₚ-lookup (nonEmpty (_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (fsuc fzero) = x₁ ∘ sym
∉ₚ-lookup (nonEmpty (_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (fsuc (fsuc ()))
∉ₚ-lookup (nonEmpty (_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) fzero = x ∘ sym
∉ₚ-lookup (nonEmpty (_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (fsuc fzero) = x₁ ∘ sym
∉ₚ-lookup (nonEmpty (_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (fsuc (fsuc k)) =
  ∉ₚ-lookup (nonEmpty e p e⇿p₁ e∉p₁) i∉p (fsuc k)

∉ₚ-lookup₂ : ∀ {n} {p : Path n} (p⁺ : NonEmpty p) →
            ∀ {i j} → (i , j) ⇿ p → ∀ k → lookupᵥ p⁺ (fsuc k) ≢ j
∉ₚ-lookup₂ (nonEmpty (j , l) p  e⇿p e∉p) (continue x) fzero    = ij⇿p⇒i≢j e⇿p ∘ sym
∉ₚ-lookup₂ (nonEmpty (j , l) [] e⇿p e∉p) (continue x) (fsuc ())
∉ₚ-lookup₂ (nonEmpty (j , l) ((_ , _) ∷ p ∣ _ ∣ _) _ (notHere _ j≢l _)) (continue _) (fsuc fzero) = j≢l ∘ sym
∉ₚ-lookup₂ (nonEmpty (j , l) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) _ e∉p) (continue x) (fsuc (fsuc k)) =
  ∉ₚ-lookup (nonEmpty e p e⇿p₁ e∉p₁) e∉p (fsuc (fsuc k))

lookup! : ∀ {n} {p : Path n} (p⁺ : NonEmpty p) → ∀ k l → k ≢ l → lookupᵥ p⁺ k ≢ lookupᵥ p⁺ l
lookup! (nonEmpty e p e⇿p e∉p)               fzero           fzero           0≢0 = contradiction refl 0≢0
lookup! (nonEmpty e p e⇿p e∉p)               fzero           (fsuc fzero)    _   = ij⇿p⇒i≢j e⇿p
lookup! (nonEmpty e [] e⇿p e∉p)              fzero           (fsuc (fsuc ()))
lookup! (nonEmpty e p e⇿p e∉p)               (fsuc fzero)    fzero           _   = ij⇿p⇒i≢j e⇿p ∘ sym
lookup! (nonEmpty e [] e⇿p e∉p)              (fsuc (fsuc ())) _
lookup! (nonEmpty e p e⇿p e∉p)               (fsuc fzero)    (fsuc fzero)    1≢1 = contradiction refl 1≢1
lookup! (nonEmpty e [] e⇿p e∉p)              (fsuc fzero)    (fsuc (fsuc ()))
lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) fzero           (fsuc (fsuc l)) _   =
  (∉ₚ-lookup (nonEmpty f p a b) e∉p (fsuc l)) ∘ sym
lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (fsuc (fsuc k)) fzero           _   =
  (∉ₚ-lookup (nonEmpty f p a b) e∉p (fsuc k))
lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (fsuc fzero)    (fsuc (fsuc l)) _   =
  ∉ₚ-lookup₂ (nonEmpty f p a b) e⇿p l ∘ sym
lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (fsuc (fsuc k)) (fsuc fzero)    _   =
  ∉ₚ-lookup₂ (nonEmpty f p a b) e⇿p k
lookup! (nonEmpty e (_ ∷ _ ∣ _ ∣ _) e⇿p e∉p) (fsuc (fsuc k)) (fsuc (fsuc l)) k≢l =
  lookup! (nonEmpty _ _ _ _) (fsuc k) (fsuc l) (k≢l ∘ cong fsuc)

----------------------------------------------------------------------------
-- length

length-cong : ∀ {n} {p q : Path n} → p ≈ₚ q → length p ≡ length q
length-cong []        = refl
length-cong (_ ∷ p≈ₚq) = cong suc (length-cong p≈ₚq)

|p|<n : ∀ {n} {p : Path n} → NonEmpty p → length p <ℕ n
|p|<n {n} q@(nonEmpty e p e⇿p e∉p) with suc (length p) <? n
... | yes |q|<n = |q|<n
... | no  |q|≮n with pigeonhole (≰⇒> |q|≮n) (lookupᵥ q)
...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookup! q i j i≢j)

|p|≤n : ∀ {n} (p : Path n) → length p ≤ℕ n
|p|≤n []                  = z≤n
|p|≤n (e ∷ p ∣ e⇿p ∣ e∉p) = <⇒≤ (|p|<n (nonEmpty _ _ e⇿p e∉p))

----------------------------------------------------------------------------
-- _⇨[_]⇨_

⇨[]⇨-resp-≈ₚ : ∀ {n i j} {p q : Path n} → p ≈ₚ q → i ⇨[ p ]⇨ j → i ⇨[ q ]⇨ j
⇨[]⇨-resp-≈ₚ [] ⇨[]⇨ = ⇨[]⇨
⇨[]⇨-resp-≈ₚ (refl ∷ p≈q) (⇨∷⇨ x) = ⇨∷⇨ (⇨[]⇨-resp-≈ₚ p≈q x)
