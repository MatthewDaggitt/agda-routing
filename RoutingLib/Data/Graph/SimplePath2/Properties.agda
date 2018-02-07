open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Decidable; Total; _⇒_; Reflexive; Symmetric; Antisymmetric; Transitive; _Respects_; tri≈; tri<; tri>; IsEquivalence; IsDecEquivalence; Setoid; DecSetoid; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (ℕ; suc; z≤n; s≤s) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; m≢1+m+n; <⇒≢; <⇒≯; ≤-refl; m+n≮n; suc-injective; <-cmp)
open import Data.Fin using (Fin; _<_; _≤?_) renaming (suc to fsuc)
open import Data.Fin.Properties using (cmp; ≤-trans; ≤-antisym; ≤-total; _<?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)

open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath2
open import RoutingLib.Data.Graph.SimplePath2.NonEmpty as NE using ()
open import RoutingLib.Data.Graph.SimplePath2.NonEmpty.Properties as NEP using ()
open import RoutingLib.Data.Nat.Properties using (n≢1+n)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)

module RoutingLib.Data.Graph.SimplePath2.Properties {n : ℕ} where

  abstract

    --------------
    -- Equality --
    --------------

    ≈-refl : Reflexive (_≈_ {n})
    ≈-refl {invalid} = invalid
    ≈-refl {valid p} = valid NEP.≈-refl

    ≈-reflexive : _≡_ ⇒ (_≈_ {n})
    ≈-reflexive refl = ≈-refl

    ≈-sym : Symmetric (_≈_ {n})
    ≈-sym invalid     = invalid
    ≈-sym (valid p≈q) = valid (NEP.≈-sym p≈q)

    ≈-trans : Transitive (_≈_ {n})
    ≈-trans invalid     invalid     = invalid
    ≈-trans (valid p≈q) (valid q≈r) = valid (NEP.≈-trans p≈q q≈r)

    _≟_ : Decidable (_≈_ {n})
    invalid ≟ invalid = yes invalid
    invalid ≟ valid q = no λ()
    valid p ≟ invalid  = no λ()
    valid p ≟ valid q with p NEP.≟ q
    ... | no  p≉q = no (λ{(valid p≈q) → p≉q p≈q})
    ... | yes p≈q = yes (valid p≈q)

    ≈-isEquivalence : IsEquivalence (_≈_ {n})
    ≈-isEquivalence = record
      { refl  = ≈-refl
      ; sym   = ≈-sym
      ; trans = ≈-trans
      }

    ≈-isDecEquivalence : IsDecEquivalence (_≈_ {n})
    ≈-isDecEquivalence = record
      { isEquivalence = ≈-isEquivalence
      ; _≟_           = _≟_
      }

  ℙₛ : Setoid lzero lzero
  ℙₛ = record 
    { Carrier       = SimplePath n 
    ; _≈_           = _≈_ 
    ; isEquivalence = ≈-isEquivalence 
    }

  Decℙₛ : DecSetoid lzero lzero
  Decℙₛ = record 
    { Carrier          = SimplePath n 
    ; _≈_              = _≈_ 
    ; isDecEquivalence = ≈-isDecEquivalence 
    }

  abstract

  
    -- Linkage

    _⇿?_ : Decidable (_⇿_ {n})
    e ⇿? invalid = no λ()
    e ⇿? valid p with e NEP.⇿? p
    ... | yes e⇿p = yes (valid e⇿p)
    ... | no ¬e⇿p = no λ{(valid e⇿p) → ¬e⇿p e⇿p}

    ⇿-resp-≈ : ∀ {e} {p q : SimplePath n} → p ≈ q → e ⇿ p → e ⇿ q
    ⇿-resp-≈ invalid     e⇿p         = e⇿p
    ⇿-resp-≈ (valid p≈q) (valid e⇿p) = valid (NEP.⇿-resp-≈ p≈q e⇿p)
    
    -- Membership

    _∉?_ : Decidable (_∉_ {n})
    k ∉? invalid     = yes invalid
    k ∉? valid p with k NEP.∉? p
    ... | yes k∉p = yes (valid k∉p)
    ... | no  k∈p = no λ{(valid k∉p) → k∈p k∉p}

    ∉-resp-≈ : ∀ {k : Fin n} → (k ∉_) Respects _≈_
    ∉-resp-≈ invalid     invalid     = invalid
    ∉-resp-≈ (valid p≈q) (valid k∉p) = valid (NEP.∉-resp-≈ p≈q k∉p)

{-
    ∈-resp-≈ : ∀ {k : Fin n} → (k ∈_) Respects _≈_
    ∈-resp-≈ x≈y k∈x k∉y = k∈x (∉-resp-≈ (≈-sym x≈y) k∉y)
 -}
 
    -- Graph membership
{-
    _∈𝔾?_ : ∀ {a} {A : Set a} → Decidable (_∈𝔾_ {a} {n} {A})
    invalid     ∈𝔾? G = no λ()
    valid p    ∈𝔾? G = yes valid p
    [ p ] ∈𝔾? G with p NEP.∈𝔾? G
    ... | yes p∈G = yes [ p∈G ]
    ... | no  p∉G = no (λ {[ p∈G ] → p∉G p∈G})

    _∉𝔾?_ : ∀ {a} {A : Set a} → Decidable (_∉𝔾_ {a} {n} {A})
    p ∉𝔾? G with p ∈𝔾? G
    ... | yes p∈G = no (λ p∉G → p∉G p∈G)
    ... | no  p∉G = yes p∉G

    ∈𝔾-resp-≈ : ∀ {a} {A : Set a} {G : Graph A n} → (_∈𝔾 G) Respects _≈_
    ∈𝔾-resp-≈ valid p      valid p      = valid p
    ∈𝔾-resp-≈ [ p≈q ] [ p∈G ] = [ NEP.∈𝔾-resp-≈ p≈q p∈G ]

    ∉𝔾-resp-≈ : ∀ {a} {A : Set a} {G : Graph A n} → (_∉𝔾 G) Respects _≈_
    ∉𝔾-resp-≈ p≈q p∉G q∈G = contradiction (∈𝔾-resp-≈ (≈-sym p≈q) q∈G) p∉G
    
-}
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

    -- Length
    length<n : (p : SimplePath (suc n)) → length p <ℕ suc n
    length<n invalid                     = s≤s z≤n
    length<n (valid [])                  = s≤s z≤n
    length<n (valid (e ∷ p ∣ e⇿p ∣ e∉p)) = NEP.|p|<n (NE.nonEmpty e p e⇿p e∉p)
    
    length-cong : ∀ {p q : SimplePath n} → p ≈ q → length p ≡ length q
    length-cong invalid     = refl
    length-cong (valid p≈q) = NEP.length-cong p≈q

    ∷ₐ-cong : ∀ (e : Fin n × Fin n) → (e ∷ₐ_) Preserves _≈_ ⟶ _≈_
    ∷ₐ-cong (i , j) invalid     = invalid
    ∷ₐ-cong (i , j) {valid p} {valid q} (valid p≈q) with (i , j) NEP.⇿? p | (i , j) NEP.⇿? q | i NEP.∉? p | i NEP.∉? q
    ... | no _     | no _     | _       | _       = invalid
    ... | no ¬ij⇿p | yes ij⇿q | _       | _       = contradiction (NEP.⇿-resp-≈ (NEP.≈-sym p≈q) ij⇿q) ¬ij⇿p
    ... | yes ij⇿p | no ¬ij⇿q | _       | _       = contradiction (NEP.⇿-resp-≈ p≈q ij⇿p) ¬ij⇿q
    ... | yes _    | yes _    | no _    | no _    = invalid
    ... | yes _    | yes _    | no  i∈p | yes i∉q = contradiction (NEP.∉-resp-≈ (NEP.≈-sym p≈q) i∉q) i∈p
    ... | yes _    | yes _    | yes i∉p | no  i∈p = contradiction (NEP.∉-resp-≈ p≈q i∉p) i∈p
    ... | yes _    | yes _    | yes _   | yes _   = valid (refl ∷ p≈q)
    
    ∷ₐ-accept : ∀ {i j : Fin n} {p} (ij⇿p : (i , j) NE.⇿ p) (i∉p : i NE.∉ p) →
                (i , j) ∷ₐ valid p ≈ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)
    ∷ₐ-accept {i} {j} {p} il⇿p i∉p with (i , j) NEP.⇿? p | i NEP.∉? p
    ... | no ¬ij⇿p | _       = contradiction il⇿p ¬ij⇿p
    ... | _        | no  i∈p = contradiction i∉p i∈p
    ... | yes ij⇿p | yes _   = valid (refl ∷ NEP.≈-refl)

    ∷ₐ-reject : ∀ {i j : Fin n} {p} → ¬ ((i , j) ⇿ p) ⊎ i ∈ p → (i , j) ∷ₐ p ≈ invalid
    ∷ₐ-reject {p = invalid} _            = invalid
    ∷ₐ-reject {i} {j} {p = valid p} ¬ij⇿p⊎i∈p  with (i , j) NEP.⇿? p | i NEP.∉? p
    ... | no  _    | _       = invalid
    ... | yes _    | no  _   = invalid
    ... | yes ij⇿p | yes i∉p   with ¬ij⇿p⊎i∈p
    ...   | inj₁ ¬ij⇿p = contradiction (valid ij⇿p) ¬ij⇿p
    ...   | inj₂ i∈p   = contradiction (valid i∉p) i∈p

    ∷ₐ-length : ∀ (i j : Fin n) p {q} → (i , j) ∷ₐ p ≈ valid q →
                length ((i , j) ∷ₐ p) ≡ suc (length p)
    ∷ₐ-length i j invalid   ()
    ∷ₐ-length i j (valid p) ij∷p≈q with (i , j) NEP.⇿? p | i NEP.∉? p
    ... | no  _ | _     = contradiction ij∷p≈q λ()
    ... | yes _ | no  _ = contradiction ij∷p≈q λ()
    ... | yes _ | yes _ = refl
{-
    weight-cong : ∀ {a b} {A : Set a} {B : Set b} _▷_ (1# : B) {p q : SimplePath n} {G : Graph A n} (p≈q : p ≈ q) (p∈G : p ∈𝔾 G) (q∈G : q ∈𝔾 G) → weight _▷_ 1# p∈G ≡ weight _▷_ 1# q∈G
    weight-cong _▷_ 1# valid p      valid p      valid p      = refl
    weight-cong _▷_ 1# [ p≈q ] [ p∈G ] [ q∈G ] = NEP.weight-cong _▷_ 1# p≈q p∈G q∈G
-}
