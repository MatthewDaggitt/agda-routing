open import Relation.Binary using (Decidable; Total; Reflexive; Symmetric; Antisymmetric; Transitive; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (suc; z≤n; s≤s) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans)
open import Data.Fin using (Fin; _<_; _≤?_) renaming (suc to fsuc)
open import Data.Fin.Properties using (cmp)
open import Data.Sum using (inj₁; inj₂)

open import RoutingLib.Data.Graph.SimplePath
open import RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties as NEP using ()
open import RoutingLib.Data.Nat.Properties using (<⇒≢; <⇒≯; ≤-refl; m+n≮n; m+1+n≢n; suc-injective) renaming (cmp to ≤ℕ-cmp)
open import RoutingLib.Data.Fin.Properties using (≤-trans; ≤-antisym; ≤-total; _<?_)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)

module RoutingLib.Data.Graph.SimplePath.Properties {n} where

  open import RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties using (p≈q⇒p₀≡q₀; p≉i∷p) public

  abstract

    ------------
    -- SPaths --
    ------------

    -- Equality

    ≈-refl : Reflexive (_≈_ {n})
    ≈-refl {[]}    = []
    ≈-refl {[ _ ]} = [ NEP.≈-refl ]

    ≈-sym : Symmetric (_≈_ {n})
    ≈-sym [] = []
    ≈-sym [ p≈q ] = [ NEP.≈-sym p≈q ]

    ≈-trans : Transitive (_≈_ {n})
    ≈-trans [] [] = []
    ≈-trans [ p≈q ] [ q≈r ] = [ NEP.≈-trans p≈q q≈r ]

    _≟_ : Decidable (_≈_ {n})
    []    ≟ []    = yes []
    []    ≟ [ _ ] = no λ()
    [ _ ] ≟ []    = no λ()
    [ p ] ≟ [ q ] with p NEP.≟ q
    ... | no  p≉q = no (λ{[ p≈q ] → p≉q p≈q})
    ... | yes p≈q = yes [ p≈q ]


    -- Membership
  
    _∉?_ : Decidable (_∉_ {n})
    k ∉? []    = yes []
    k ∉? [ p ] with k NEP.∉? p
    ... | yes k∉p = yes [ k∉p ]
    ... | no  k∈p = no λ{[ k∉p ] → k∈p k∉p}

    ≈-pres-∉ : ∀ {p q} {k : Fin n} → k ∉ p → p ≈ q → k ∉ q
    ≈-pres-∉ []      []      = []
    ≈-pres-∉ [ k∉p ] [ p≈q ] = [ NEP.≈-pres-∉ k∉p p≈q ]

    -- Ordering

    ≤ₚ-refl : Reflexive (_≤ₚ_ {n})
    ≤ₚ-refl {[]} = stop
    ≤ₚ-refl {[ x ]} = lex refl NEP.≤ₗₑₓ-refl

    ≤ₚ-trans : Transitive (_≤ₚ_ {n})
    ≤ₚ-trans stop              _                 = stop
    ≤ₚ-trans (len |p|<|q|)     (len |q|<|r|)     = len (<-trans |p|<|q| |q|<|r|)
    ≤ₚ-trans (len |p|<|q|)     (lex |q|≡|r| _)   = len (subst (_ <ℕ_) |q|≡|r| |p|<|q|)
    ≤ₚ-trans (lex |p|≡|q| _)   (len |q|<|r|)     = len (subst (_<ℕ _) (sym |p|≡|q|) |q|<|r|)
    ≤ₚ-trans (lex |p|≡|q| p≤q) (lex |q|≡|r| q≤r) = lex (trans |p|≡|q| |q|≡|r|) (NEP.≤ₗₑₓ-trans p≤q q≤r)

    ≤ₚ-antisym : Antisymmetric _≈_ (_≤ₚ_ {n})
    ≤ₚ-antisym stop            stop            = []
    ≤ₚ-antisym (len |p|<|q|)   (len |q|<|p|)   = contradiction |p|<|q| (<⇒≯ |q|<|p|)
    ≤ₚ-antisym (len |p|<|q|)   (lex |q|≡|p| _) = contradiction (sym |q|≡|p|) (<⇒≢ |p|<|q|)
    ≤ₚ-antisym (lex |p|≡|q| _) (len |q|<|p|)   = contradiction (sym |p|≡|q|) (<⇒≢ |q|<|p|)
    ≤ₚ-antisym (lex _ p≤q)     (lex _ q≤p)     = [ NEP.≤ₗₑₓ-antisym p≤q q≤p ]

    _≤ₚ?_ : Decidable (_≤ₚ_ {n})
    []    ≤ₚ? _ = yes stop
    [ _ ] ≤ₚ? [] = no λ()
    [ p ] ≤ₚ? [ q ] with suc (length [ p ]) ≤ℕ? length [ q ] | length [ p ] ≟ℕ length [ q ] | p NEP.≤ₗₑₓ? q
    ... | yes |p|<|q| | _           | _       = yes (len |p|<|q|)
    ... | no  |p|≮|q| | no  |p|≢|q| | _       = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex |p|≡|q| _) → |p|≢|q| |p|≡|q|})
    ... | no  |p|≮|q| | _           | no  p≰q = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex _ p≤q) → p≰q p≤q})
    ... | no  _       | yes |p|≡|q| | yes p≤q = yes (lex |p|≡|q| p≤q)
  
    ≤ₚ-total : Total (_≤ₚ_ {n})
    ≤ₚ-total [] _ = inj₁ stop
    ≤ₚ-total _ [] = inj₂ stop
    ≤ₚ-total [ p ] [ q ] with ≤ℕ-cmp (length [ p ]) (length [ q ])
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
    ≤ₚ-resp-≈ []      _       stop              = stop
    ≤ₚ-resp-≈ [ p≈q ] [ r≈s ] (len |p|<|q|)     rewrite NEP.p≈q⇒|p|≡|q| p≈q | NEP.p≈q⇒|p|≡|q| r≈s = len |p|<|q|
    ≤ₚ-resp-≈ [ p≈q ] [ r≈s ] (lex |p|≡|q| p≤q) rewrite NEP.p≈q⇒|p|≡|q| p≈q | NEP.p≈q⇒|p|≡|q| r≈s = lex |p|≡|q| (NEP.≤ₗₑₓ-resp-≈ p≈q r≈s p≤q)

    i∷p≰p : ∀ {i : Fin n} {p} {i∉p} → [ i ∷ p ∣ i∉p ] ≰ₚ [ p ]
    i∷p≰p (len 1+|p|<|p|)   = contradiction 1+|p|<|p| (m+n≮n 1 _)
    i∷p≰p (lex 1+|p|≡|p| _) = contradiction 1+|p|≡|p| (m+1+n≢n 0 _)

    length<n : (p : SimplePath (suc n)) → length p <ℕ (suc n)
    length<n []    = s≤s z≤n
    length<n [ p ] = NEP.|p|<n p
