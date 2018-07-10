open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Decidable; Total; _⇒_; Reflexive; Symmetric; Antisymmetric; Transitive; _Respects_; tri≈; tri<; tri>; IsEquivalence; IsDecEquivalence; Setoid; DecSetoid; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (ℕ; suc; z≤n; s≤s) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≤-trans; m≢1+m+n; <⇒≢; <⇒≯; ≤-refl; m+n≮n; suc-injective; <-cmp)
open import Data.Fin using (Fin; _<_; _≤?_; suc; zero)
open import Data.Fin.Properties using (cmp; ≤-antisym; ≤-total; _<?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)

open import RoutingLib.Data.SimplePath
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.NonEmpty as NE using (SimplePathⁿᵗ)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties as NEP using ()
open import RoutingLib.Data.Nat.Properties using (n≢1+n)

module RoutingLib.Data.SimplePath.Properties {n : ℕ} where

  abstract

    ----------------------------------------------------------------------------
    -- Linkage

    _⇿?_ : Decidable (_⇿_ {n})
    e ⇿? invalid = no λ()
    e ⇿? valid p with e NEP.⇿? p
    ... | yes e⇿p = yes (valid e⇿p)
    ... | no ¬e⇿p = no λ{(valid e⇿p) → ¬e⇿p e⇿p}

    ⇿-resp-≈ₚ : ∀ {e : Fin n × Fin n} → (e ⇿_) Respects _≈ₚ_
    ⇿-resp-≈ₚ invalid     e⇿p         = e⇿p
    ⇿-resp-≈ₚ (valid p≈q) (valid e⇿p) = valid (NEP.⇿-resp-≈ₚ p≈q e⇿p)

    ----------------------------------------------------------------------------
    -- Membership

    _∉?_ : Decidable (_∉_ {n})
    k ∉? invalid     = yes invalid
    k ∉? valid p with k NEP.∉? p
    ... | yes k∉p = yes (valid k∉p)
    ... | no  k∈p = no λ{(valid k∉p) → k∈p k∉p}

    ∉-resp-≈ₚ : ∀ {k : Fin n} → (k ∉_) Respects _≈ₚ_
    ∉-resp-≈ₚ invalid     invalid     = invalid
    ∉-resp-≈ₚ (valid p≈q) (valid k∉p) = valid (NEP.∉-resp-≈ₚ p≈q k∉p)

    ∈-resp-≈ₚ : ∀ {k : Fin n} → (k ∈_) Respects _≈ₚ_
    ∈-resp-≈ₚ x≈y k∈x k∉y = k∈x (∉-resp-≈ₚ (≈ₚ-sym x≈y) k∉y)

    ----------------------------------------------------------------------------
    -- Length

    length<n : (p : SimplePath (suc n)) → length p <ℕ suc n
    length<n invalid                     = s≤s z≤n
    length<n (valid [])                  = s≤s z≤n
    length<n (valid (e ∷ p ∣ e⇿p ∣ e∉p)) = NEP.|p|<n (NE.nonEmpty e p e⇿p e∉p)

    length≤1+n : (p : SimplePath n) → length p ≤ℕ suc n
    length≤1+n invalid   = z≤n
    length≤1+n (valid p) = NEP.|p|≤1+n p

    length-cong : ∀ {p q : SimplePath n} → p ≈ₚ q → length p ≡ length q
    length-cong invalid     = refl
    length-cong (valid p≈q) = NEP.length-cong p≈q

    ----------------------------------------------------------------------------
    -- Other

    -- Ordering
{-
    ≤ₚ-refl : Reflexive (_≤ₚ_ {n})
    ≤ₚ-refl {invalid}     = empty
    ≤ₚ-refl {valid p}    = stop₁
    ≤ₚ-refl {[ x ]} = lex refl NEP.≤ₗₑₓ-refl

    ≤ₚ-trans : Transitive (_≤ₚ_ {n})
    ≤ₚ-trans empty             _                 = empty
    ≤ₚ-trans stop₁             p≤q               = p≤q
    ≤ₚ-trans stop₂             (len _ )          = stop₂
    ≤ₚ-trans stop₂             (lex _ _)         = stop₂
    ≤ₚ-trans (len |p|<|q|)     (len |q|<|r|)     = len (<-trans |p|<|q| |q|<|r|)
    ≤ₚ-trans (len |p|<|q|)     (lex |q|≡|r| _)   = len (subst (_ <ℕ_) |q|≡|r| |p|<|q|)
    ≤ₚ-trans (lex |p|≡|q| _)   (len |q|<|r|)     = len (subst (_<ℕ _) (sym |p|≡|q|) |q|<|r|)
    ≤ₚ-trans (lex |p|≡|q| p≤q) (lex |q|≡|r| q≤r) = lex (trans |p|≡|q| |q|≡|r|) (NEP.≤ₗₑₓ-trans p≤q q≤r)

    ≤ₚ-antisym : Antisymmetric _≈_ (_≤ₚ_ {n})
    ≤ₚ-antisym empty empty = invalid
    ≤ₚ-antisym stop₁ stop₁ = valid p
    ≤ₚ-antisym stop₂ ()
    ≤ₚ-antisym (len |p|<|q|)   (len |q|<|p|)   = contradiction |p|<|q| (<⇒≯ |q|<|p|)
    ≤ₚ-antisym (len |p|<|q|)   (lex |q|≡|p| _) = contradiction (sym |q|≡|p|) (<⇒≢ |p|<|q|)
    ≤ₚ-antisym (lex |p|≡|q| _) (len |q|<|p|)   = contradiction (sym |p|≡|q|) (<⇒≢ |q|<|p|)
    ≤ₚ-antisym (lex _ p≤q)     (lex _ q≤p)     = [ NEP.≤ₗₑₓ-antisym p≤q q≤p ]

    _≤ₚ?_ : Decidable (_≤ₚ_ {n})
    invalid     ≤ₚ? _     = yes empty
    valid p    ≤ₚ? invalid     = no λ()
    valid p    ≤ₚ? valid p    = yes stop₁
    valid p    ≤ₚ? [ _ ] = yes stop₂
    [ _ ] ≤ₚ? invalid     = no λ()
    [ _ ] ≤ₚ? valid p    = no λ()
    [ p ] ≤ₚ? [ q ] with suc (length [ p ]) ≤ℕ? length [ q ] | length [ p ] ≟ℕ length [ q ] | p NEP.≤ₗₑₓ? q
    ... | yes |p|<|q| | _           | _       = yes (len |p|<|q|)
    ... | no  |p|≮|q| | no  |p|≢|q| | _       = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex |p|≡|q| _) → |p|≢|q| |p|≡|q|})
    ... | no  |p|≮|q| | _           | no  p≰q = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex _ p≤q) → p≰q p≤q})
    ... | no  _       | yes |p|≡|q| | yes p≤q = yes (lex |p|≡|q| p≤q)

    ≤ₚ-total : Total (_≤ₚ_ {n})
    ≤ₚ-total invalid     _     = inj₁ empty
    ≤ₚ-total _     invalid     = inj₂ empty
    ≤ₚ-total valid p    valid p    = inj₁ stop₁
    ≤ₚ-total valid p    [ _ ] = inj₁ stop₂
    ≤ₚ-total [ _ ] valid p    = inj₂ stop₂
    ≤ₚ-total [ p ] [ q ] with <-cmp (length [ p ]) (length [ q ])
    ≤ₚ-total [ _ ] [ _ ] | tri< |p|<|q| _ _ = inj₁ (len |p|<|q|)
    ≤ₚ-total [ _ ] [ _ ] | tri> _ _ |p|<|q| = inj₂ (len |p|<|q|)
    ≤ₚ-total [ i ∺ j ∣ _ ] [ k ∺ l ∣ _ ] | tri≈ _ _ _ with cmp i k | ≤-total j l
    ... | tri< i<k _ _ | _        = inj₁ (lex refl (stopSecond i<k))
    ... | tri> _ _ k<i | _        = inj₂ (lex refl (stopSecond k<i))
    ... | tri≈ _ k≡i _ | inj₁ j≤l = inj₁ (lex refl (stopFirst k≡i j≤l))
    ... | tri≈ _ k≡i _ | inj₂ l≤j = inj₂ (lex refl (stopFirst (sym k≡i) l≤j))
    ≤ₚ-total [ i ∺ j ∣ _ ] [ k ∷ (_ ∷ _ ∣ _) ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∺ j ∣ _ ] [ k ∷ (_ ∺ _ ∣ _) ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∷ (_ ∷ _ ∣ _) ∣ _ ] [ k ∺ l ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∷ (_ ∺ _ ∣ _) ∣ _ ] [ k ∺ l ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∷ p ∣ _ ] [ k ∷ q ∣ _ ] | tri≈ _ |p|≡|q| _ with cmp i k | ≤ₚ-total [ p ] [ q ]
    ... | tri< i<k _ _ | _        = inj₁ (lex |p|≡|q| (stepUnequal i<k))
    ... | tri> _ _ k<i | _        = inj₂ (lex (sym |p|≡|q|) (stepUnequal k<i))
    ... | tri≈ _ _   _ | inj₁ (len |p|<|q|) = contradiction (suc-injective |p|≡|q|) (<⇒≢ |p|<|q|)
    ... | tri≈ _ i≡k _ | inj₁ (lex _ p≤q) = inj₁ (lex |p|≡|q| (stepEqual i≡k p≤q))
    ... | tri≈ _ i≡k _ | inj₂ (len |q|<|p|) = contradiction (suc-injective (sym |p|≡|q|)) (<⇒≢ |q|<|p|)
    ... | tri≈ _ i≡k _ | inj₂ (lex _ q≤p) = inj₂ (lex (sym |p|≡|q|) (stepEqual (sym i≡k) q≤p))

    ≤ₚ-resp-≈ : (_≤ₚ_ {n}) RespectedBy _≈_
    ≤ₚ-resp-≈ invalid       _       _ = empty
    ≤ₚ-resp-≈ valid p      invalid       ()
    ≤ₚ-resp-≈ valid p      valid p      _ = stop₁
    ≤ₚ-resp-≈ valid p      [ _ ]   _ = stop₂
    ≤ₚ-resp-≈ [ p≈q ] [ r≈s ] (len |p|<|q|)     rewrite NEP.p≈q⇒|p|≡|q| p≈q | NEP.p≈q⇒|p|≡|q| r≈s = len |p|<|q|
    ≤ₚ-resp-≈ [ p≈q ] [ r≈s ] (lex |p|≡|q| p≤q) rewrite NEP.p≈q⇒|p|≡|q| p≈q | NEP.p≈q⇒|p|≡|q| r≈s = lex |p|≡|q| (NEP.≤ₗₑₓ-resp-≈ p≈q r≈s p≤q)

    i∷p≰p : ∀ {i : Fin n} {p} {i∉p} → [ i ∷ p ∣ i∉p ] ≰ₚ [ p ]
    i∷p≰p (len 1+|p|<|p|)   = contradiction 1+|p|<|p| (m+n≮n 1 _)
    i∷p≰p (lex 1+|p|≡|p| _) = contradiction (sym 1+|p|≡|p|) (n≢1+n _)
-}




{-
    ∷ₐ-cong : ∀ (e : Fin n × Fin n) → (e ∷ₐ_) Preserves _≈ₚ_ ⟶ _≈ₚ_
    ∷ₐ-cong (i , j) invalid     = invalid
    ∷ₐ-cong (i , j) {valid p} {valid q} (valid p≈q) with (i , j) NEP.⇿? p | (i , j) NEP.⇿? q | i NEP.∉? p | i NEP.∉? q
    ... | no _     | no _     | _       | _       = invalid
    ... | no ¬ij⇿p | yes ij⇿q | _       | _       = contradiction (NEP.⇿-resp-≈ₚ (NEP.≈ₚ-sym p≈q) ij⇿q) ¬ij⇿p
    ... | yes ij⇿p | no ¬ij⇿q | _       | _       = contradiction (NEP.⇿-resp-≈ₚ p≈q ij⇿p) ¬ij⇿q
    ... | yes _    | yes _    | no _    | no _    = invalid
    ... | yes _    | yes _    | no  i∈p | yes i∉q = contradiction (NEP.∉-resp-≈ₚ (NEP.≈ₚ-sym p≈q) i∉q) i∈p
    ... | yes _    | yes _    | yes i∉p | no  i∈p = contradiction (NEP.∉-resp-≈ₚ p≈q i∉p) i∈p
    ... | yes _    | yes _    | yes _   | yes _   = valid (refl ∷ p≈q)

    ∷ₐ-accept : ∀ {i j : Fin n} {p} (ij⇿p : (i , j) NE.⇿ p) (i∉p : i NE.∉ p) →
                (i , j) ∷ₐ valid p ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)
    ∷ₐ-accept {i} {j} {p} il⇿p i∉p with (i , j) NEP.⇿? p | i NEP.∉? p
    ... | no ¬ij⇿p | _       = contradiction il⇿p ¬ij⇿p
    ... | _        | no  i∈p = contradiction i∉p i∈p
    ... | yes ij⇿p | yes _   = valid (refl ∷ NEP.≈ₚ-refl)

    ∷ₐ-reject : ∀ {i j : Fin n} {p} → ¬ ((i , j) ⇿ p) ⊎ i ∈ p → (i , j) ∷ₐ p ≈ₚ invalid
    ∷ₐ-reject {p = invalid} _            = invalid
    ∷ₐ-reject {i} {j} {p = valid p} ¬ij⇿p⊎i∈p  with (i , j) NEP.⇿? p | i NEP.∉? p
    ... | no  _    | _       = invalid
    ... | yes _    | no  _   = invalid
    ... | yes ij⇿p | yes i∉p   with ¬ij⇿p⊎i∈p
    ...   | inj₁ ¬ij⇿p = contradiction (valid ij⇿p) ¬ij⇿p
    ...   | inj₂ i∈p   = contradiction (valid i∉p) i∈p

    ∷ₐ-length : ∀ (i j : Fin n) p {q} → (i , j) ∷ₐ p ≈ₚ valid q →
                length ((i , j) ∷ₐ p) ≡ suc (length p)
    ∷ₐ-length i j invalid   ()
    ∷ₐ-length i j (valid p) ij∷p≈q with (i , j) NEP.⇿? p | i NEP.∉? p
    ... | no  _ | _     = contradiction ij∷p≈q λ()
    ... | yes _ | no  _ = contradiction ij∷p≈q λ()
    ... | yes _ | yes _ = refl
-}
