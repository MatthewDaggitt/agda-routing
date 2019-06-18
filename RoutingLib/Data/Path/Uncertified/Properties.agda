

module RoutingLib.Data.Path.Uncertified.Properties where

open import Data.List.Any using (any; there; here)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin.Properties using (pigeonhole)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Level using (0ℓ)
open import Function using (_∘_; flip)
open import Data.Product.Properties using (≡-dec)
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Nat.Properties using (<⇒≤suc)
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.DecTotalOrder
  as ToStrict

open import RoutingLib.Data.Path.Uncertified

open ≡-Reasoning

----------------------------------------------------------------------------
-- Edges

_≟ₑ_ : Decidable {A = Edge} _≡_
_≟ₑ_ = ≡-dec _≟_ _≟_

𝕍ₛ : Setoid _ _
𝕍ₛ = setoid Vertex

𝔼ₛ : Setoid _ _
𝔼ₛ = setoid Edge

----------------------------------------------------------------------------
-- Linking

_⇿?_ : Decidable _⇿_
(i , j) ⇿? [] with i ≟ j
... | yes i≡j = no  λ{(start i≢j) → i≢j i≡j}
... | no  i≢j = yes (start i≢j)
(i , j) ⇿? ((k , l) ∷ p) with i ≟ j | j ≟ k
... | yes i≡j | _        = no λ{(continue i≢j) → i≢j i≡j}
... | no  _   | no  j≢k  = no λ{(continue _) → j≢k refl}
... | no  i≢j | yes refl = yes (continue i≢j)

⇿-resp-≈ₚ : ∀ {e} → (e ⇿_) Respects _≈ₚ_
⇿-resp-≈ₚ refl e⇿p = e⇿p

⇿-resp-p₀ : ∀ {e p q} → source p ≡ source q → e ⇿ p → e ⇿ q
⇿-resp-p₀ {e} {[]}    {[]}    eq   e⇿p            = e⇿p
⇿-resp-p₀ {e} {[]}    {y ∷ q} ()   e⇿p
⇿-resp-p₀ {e} {x ∷ p} {[]}    ()   e⇿p
⇿-resp-p₀ {e} {_ ∷ p} {_ ∷ q} refl (continue i≢j) = continue i≢j

ij⇿p⇒i≢j : ∀ {i j p} → (i , j) ⇿ p → i ≢ j
ij⇿p⇒i≢j (start    i≢j) = i≢j
ij⇿p⇒i≢j (continue i≢j) = i≢j

⇿-source⁺ : ∀ {i j p} → i ≢ j → source p ≡ just j → (i , j) ⇿ p
⇿-source⁺ {p = []}    i≢j ()
⇿-source⁺ {p = x ∷ p} i≢j refl = continue i≢j

p₀≡n⇒p≡[] : ∀ {p} → source p ≡ nothing → p ≡ []
p₀≡n⇒p≡[] {[]}    refl = refl
p₀≡n⇒p≡[] {x ∷ p} ()

----------------------------------------------------------------------------
-- Membership

_∈ₑ?_ : Decidable _∈ₑ_
k ∈ₑ? (i , j) with k ≟ i | k ≟ j
... | yes refl | _        = yes left
... | _        | yes refl = yes right
... | no  k≢i  | no  k≢j  = no λ
  { left  → k≢i refl
  ; right → k≢j refl
  }

_∈ₚ?_ : Decidable _∈ₚ_
k ∈ₚ? p = any (k ∈ₑ?_) p

∉ₚ-resp-≈ₚ : ∀ {k} → (k ∉ₚ_) Respects _≡_
∉ₚ-resp-≈ₚ refl k∉p = k∉p

∈-source : ∀ {p i} → source p ≡ just i → i ∈ₚ p
∈-source {[]}    ()
∈-source {x ∷ p} refl = here left

----------------------------------------------------------------------------
-- Equality

p≉i∷p : ∀ {e p} → ¬ (p ≈ₚ e ∷ p)
p≉i∷p {p}    ()

_≟ₚ_ : Decidable _≈ₚ_
[]      ≟ₚ []      = yes refl
[]      ≟ₚ (k ∷ q) = no λ()
(i ∷ p) ≟ₚ []      = no λ()
(i ∷ p) ≟ₚ (k ∷ q) with i ≟ₑ k | p ≟ₚ q
... | no  i≢k  | _        = no (λ{refl → i≢k refl})
... | _        | no  p≢q  = no (λ{refl → p≢q refl})
... | yes refl | yes refl = yes refl

≡ₚ-isDecEquivalence : IsDecEquivalence _≈ₚ_
≡ₚ-isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟ₚ_
  }

ℙₛ : Setoid 0ℓ 0ℓ
ℙₛ = setoid Path

ℙₛ? : DecSetoid 0ℓ 0ℓ
ℙₛ? = record { isDecEquivalence = ≡ₚ-isDecEquivalence }

----------------------------------------------------------------------------
-- Lexicographic order

≤ₗₑₓ-refl : Reflexive _≤ₗₑₓ_
≤ₗₑₓ-refl {[]}    = stop
≤ₗₑₓ-refl {i ∷ p} = step refl refl ≤ₗₑₓ-refl

≤ₗₑₓ-reflexive : _≡_ ⇒ _≤ₗₑₓ_
≤ₗₑₓ-reflexive refl = ≤ₗₑₓ-refl

≤ₗₑₓ-total : Total _≤ₗₑₓ_
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

≤ₗₑₓ-trans : Transitive _≤ₗₑₓ_
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

≤ₗₑₓ-antisym : Antisymmetric _≈ₚ_ _≤ₗₑₓ_
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

≤ₗₑₓ-minimum : Minimum _≤ₗₑₓ_ []
≤ₗₑₓ-minimum x = stop

_≤ₗₑₓ?_ : Decidable _≤ₗₑₓ_
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

≤ₗₑₓ-isTotalOrder : IsTotalOrder _≡_ _≤ₗₑₓ_
≤ₗₑₓ-isTotalOrder = record
  { isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = ≤ₗₑₓ-reflexive
      ; trans         = ≤ₗₑₓ-trans
      }
    ; antisym    = ≤ₗₑₓ-antisym
    }
  ; total        = ≤ₗₑₓ-total
  }

≤ₗₑₓ-isDecTotalOrder : IsDecTotalOrder _≡_ _≤ₗₑₓ_
≤ₗₑₓ-isDecTotalOrder = record
  { isTotalOrder = ≤ₗₑₓ-isTotalOrder
  ; _≟_          = _≟ₚ_
  ; _≤?_         = _≤ₗₑₓ?_
  }

≤ₗₑₓ-totalOrder : TotalOrder _ _ _
≤ₗₑₓ-totalOrder = record
  { isTotalOrder = ≤ₗₑₓ-isTotalOrder
  }

≤ₗₑₓ-decTotalOrder : DecTotalOrder _ _ _
≤ₗₑₓ-decTotalOrder = record
  { isDecTotalOrder = ≤ₗₑₓ-isDecTotalOrder
  }

open ToStrict ≤ₗₑₓ-decTotalOrder public
  using ()
  renaming
  ( <-trans   to <ₗₑₓ-trans
  ; <-asym    to <ₗₑₓ-asym
  ; <-irrefl  to <ₗₑₓ-irrefl
  ; <-respˡ-≈ to <ₗₑₓ-respˡ-≈ₚ
  ; <-respʳ-≈ to <ₗₑₓ-respʳ-≈ₚ
  ; <-cmp     to <ₗₑₓ-cmp
  ; <⇒≱       to <ₗₑₓ⇒≱ₗₑₓ
  ; <⇒≤       to <ₗₑₓ⇒≤ₗₑₓ
  )

p≮ₗₑₓ[] : ∀ {p} → ¬ (p <ₗₑₓ [])
p≮ₗₑₓ[] {[]}    (_ , []≉[]) = []≉[] refl
p≮ₗₑₓ[] {e ∷ p} (() , _)

∷-mono-≤ₗₑₓ : ∀ e {p q} → p ≤ₗₑₓ q → (e ∷ p) ≤ₗₑₓ (e ∷ q)
∷-mono-≤ₗₑₓ e {p} {q} p≤q =  step refl refl p≤q

----------------------------------------------------------------------------
-- length

|p|≢|q|⇒p≉q : ∀ {p q} → length p ≢ length q → p ≉ₚ q
|p|≢|q|⇒p≉q {[]}    {[]}    0≢0     = contradiction refl 0≢0
|p|≢|q|⇒p≉q {[]}    {y ∷ q} |p|≢|q| = λ()
|p|≢|q|⇒p≉q {x ∷ p} {[]}    |p|≢|q| = λ()
|p|≢|q|⇒p≉q {x ∷ p} {y ∷ q} |p|≢|q| = λ { refl → |p|≢|q| refl }

----------------------------------------------------------------------------
-- inflate

inflate-length : ∀ p n → length p ≤ length (inflate p n)
inflate-length p       zero    = ≤-refl
inflate-length []      (suc n) = ≤-refl
inflate-length (x ∷ p) (suc n) = ≤-trans (inflate-length (x ∷ p) n) (n≤1+n _)

inflate-extract : ∀ p n {i} → source p ≡ just i →
                  inflate ((i , i) ∷ p) n ≡ (i , i) ∷ inflate p n
inflate-extract p       zero    p₀≡i = refl
inflate-extract []      (suc n) ()
inflate-extract (x ∷ p) (suc n) refl = cong (_ ∷_) (inflate-extract (x ∷ p) n refl)

inflate-source : ∀ p n {i} → source p ≡ just i →
                 source (inflate p n) ≡ just i
inflate-source p       zero    eq   = eq
inflate-source []      (suc n) ()
inflate-source (x ∷ p) (suc n) refl = refl

inflate-inflate : ∀ p m n → inflate (inflate p m) n ≡ inflate p (m + n)
inflate-inflate p             zero    n       = refl
inflate-inflate []            (suc m) zero    = refl
inflate-inflate []            (suc m) (suc n) = refl
inflate-inflate ((i , j) ∷ p) (suc m) n       = begin
  inflate ((i , i) ∷ inflate ((i , j) ∷ p) m) n ≡⟨ inflate-extract _ n (inflate-source (((i , j) ∷ p)) m refl) ⟩
  (i , i) ∷ inflate (inflate ((i , j) ∷ p) m) n ≡⟨ cong ((i , i) ∷_) (inflate-inflate _ m n) ⟩
  (i , i) ∷ inflate ((i , j) ∷ p) (m + n)       ∎
  where open ≡-Reasoning

----------------------------------------------------------------------------
-- deflate

p≡[]⇒deflate[p]≡[] : ∀ {p} → p ≡ [] → deflate p ≡ []
p≡[]⇒deflate[p]≡[] refl = refl

deflate-source : ∀ p → source (deflate p) ≡ source p
deflate-source []                      = refl
deflate-source ((i , j) ∷ [])          = refl
deflate-source ((i , j) ∷ (k , l) ∷ p) with i ≟ j | j ≟ k
... | no  _    | _        = refl
... | yes _    | no  _    = refl
... | yes refl | yes refl = deflate-source ((i , l) ∷ p)

deflate-remove : ∀ p {i j} → i ≡ j → just j ≡ source p → deflate ((i , j) ∷ p) ≡ deflate p
deflate-remove []            refl ()
deflate-remove ((i , j) ∷ p) refl refl with i ≟ i
... | no i≢i   = contradiction refl i≢i
... | yes refl = refl

deflate-skip : ∀ p {i j} → i ≢ j ⊎ just j ≢ source p →
               deflate ((i , j) ∷ p) ≡ (i , j) ∷ deflate p
deflate-skip []            {i} {j} eq = refl
deflate-skip ((k , l) ∷ p) {i} {j} eq with i ≟ j | j ≟ k
... | no  _    | _        = refl
... | yes _    | no  _    = refl
... | yes refl | yes refl = contradiction eq λ
  { (inj₁ k≢k)   → k≢k refl
  ; (inj₂ jk≢jk) → jk≢jk (cong just refl)
  }

deflate-inflate : ∀ p n → deflate (inflate p n) ≡ deflate p
deflate-inflate p                       0       = refl
deflate-inflate []                      (suc n) = refl
deflate-inflate p@((i , j) ∷ [])        (suc n) = begin
   deflate ((i , i) ∷ inflate ((i , j) ∷ []) n) ≡⟨ deflate-remove (inflate p n) refl (sym (inflate-source p n refl)) ⟩
   deflate (inflate ((i , j) ∷ []) n)           ≡⟨ deflate-inflate p n ⟩
   deflate ((i , j) ∷ [])                       ∎
deflate-inflate ((i , j) ∷ q@((k , l) ∷ p)) (suc n) with i ≟ j | j ≟ k
... | no  i≢j  | _        = begin
  deflate ((i , i) ∷ inflate ((i , j) ∷ q) n) ≡⟨ deflate-remove (inflate ((i , j) ∷ q) n) refl (sym (inflate-source ((i , j) ∷ q) n refl)) ⟩
  deflate (inflate ((i , j) ∷ q) n)           ≡⟨ deflate-inflate ((i , j) ∷ q) n ⟩
  deflate ((i , j) ∷ q)                       ≡⟨ deflate-skip q (inj₁ i≢j) ⟩
  (i , j) ∷ deflate q                         ∎
... | yes _    | no  j≢k  = begin
  deflate ((i , i) ∷ inflate ((i , j) ∷ q) n) ≡⟨ deflate-remove (inflate ((i , j) ∷ q) n) refl (sym (inflate-source ((i , j) ∷ q) n refl)) ⟩
  deflate (inflate ((i , j) ∷ q) n)           ≡⟨ deflate-inflate ((i , j) ∷ q) n ⟩
  deflate ((i , j) ∷ q)                       ≡⟨ deflate-skip q (inj₂ (j≢k ∘ just-injective)) ⟩
  (i , j) ∷ deflate q                         ∎
... | yes refl | yes refl = begin
  deflate ((i , i) ∷ inflate ((i , i) ∷ q) n) ≡⟨ deflate-remove (inflate ((i , i) ∷ q) n) refl (sym (inflate-source ((i , i) ∷ q) n refl)) ⟩
  deflate (inflate ((i , i) ∷ q) n)           ≡⟨ deflate-inflate ((i , i) ∷ q) n ⟩
  deflate ((i , i) ∷ q)                       ≡⟨ deflate-remove q refl refl ⟩
  deflate q                                   ∎

deflate-idem : ∀ p → deflate (deflate p) ≡ deflate p
deflate-idem []            = refl
deflate-idem ((i , j) ∷ []) = refl
deflate-idem ((i , j) ∷ q@((k , l) ∷ p)) with i ≟ j | j ≟ k
... | no  i≢j | _       = begin
  deflate ((i , j) ∷ deflate q) ≡⟨ deflate-skip (deflate q) (inj₁ i≢j) ⟩
  (i , j) ∷ deflate (deflate q) ≡⟨ cong (_ ∷_) (deflate-idem q) ⟩
  (i , j) ∷ deflate q           ∎
... | yes _   | no  j≢k = begin
  deflate ((i , j) ∷ deflate q) ≡⟨ deflate-skip (deflate q) (inj₂ (j≢k ∘ just-injective ∘ flip trans (deflate-source q))) ⟩
  (i , j) ∷ deflate (deflate q) ≡⟨ cong (_ ∷_) (deflate-idem q) ⟩
  (i , j) ∷ deflate q           ∎
... | yes _   | yes _   = deflate-idem ((k , l) ∷ p)

∈-deflate⁻ : ∀ {v p} → v ∈ₚ deflate p → v ∈ₚ p
∈-deflate⁻ {v} {[]}                    ()
∈-deflate⁻ {v} {(i , j) ∷ []}          v∈ij = v∈ij
∈-deflate⁻ {v} {(i , j) ∷ (k , l) ∷ p} v∈p with i ≟ j | j ≟ k | v∈p
... | no  _ | _     | here  v∈ij   = here v∈ij
... | no  _ | _     | there v∈kl∷p = there (∈-deflate⁻ v∈kl∷p)
... | yes _ | no  _ | here  v∈ij   = here v∈ij
... | yes _ | no  _ | there v∈kl∷p = there (∈-deflate⁻ v∈kl∷p)
... | yes _ | yes _ | v∈p'         = there (∈-deflate⁻ v∈p')

⇿-deflate⁺ : ∀ {e p} → e ⇿ p → e ⇿ deflate p
⇿-deflate⁺ {e} {[]}                    e⇿p = e⇿p
⇿-deflate⁺ {e} {(i , j) ∷ []}          e⇿p = e⇿p
⇿-deflate⁺ {e} {(i , j) ∷ (k , l) ∷ p} e⇿p with i ≟ j | j ≟ k
... | no  _    | _        = ⇿-resp-p₀ refl e⇿p
... | yes _    | no  _    = ⇿-resp-p₀ refl e⇿p
... | yes refl | yes refl = ⇿-deflate⁺ {e} {(k , l) ∷ p} (⇿-resp-p₀ refl e⇿p)
