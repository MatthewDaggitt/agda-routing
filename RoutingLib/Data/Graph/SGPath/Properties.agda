open import Data.Nat using (ℕ; suc) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans)
open import Data.Fin using (Fin; _<_; toℕ) renaming (suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Decidable; Setoid; Total; Reflexive; Symmetric; Antisymmetric; Transitive; IsEquivalence; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; setoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Graph
open import RoutingLib.Data.Graph.SGPath
open import RoutingLib.Data.Nat.Properties using (<⇒≢; <⇒≯; ≤-refl; m+n≮n; m+1+n≢n; m≰n⇨n<m; suc-injective) renaming (cmp to ≤ℕ-cmp)
open import RoutingLib.Data.Fin.Properties using (≤-trans; ≤-antisym; ≤-total; _≤?_; _<?_; cmp)
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)

module RoutingLib.Data.Graph.SGPath.Properties {a n} {A : Set a} where

  abstract
    -------------------
    -- NonEmptySPath --
    -------------------

    -- Equality
  
    ≈ₙₑₚ-refl : ∀ {G : Graph A n} → Reflexive (_≈ₙₑₚ_ {G = G})
    ≈ₙₑₚ-refl {_} {_ ∺ _ ∣ _ ∣ _} = refl ∺ refl
    ≈ₙₑₚ-refl {_} {_ ∷ _ ∣ _ ∣ _} = refl ∷ ≈ₙₑₚ-refl

    ≈ₙₑₚ-sym : ∀ {G : Graph A n} → Symmetric (_≈ₙₑₚ_ {G = G})
    ≈ₙₑₚ-sym (refl ∺ refl) = refl ∺ refl
    ≈ₙₑₚ-sym (refl ∷ p≈q)  = refl ∷ (≈ₙₑₚ-sym p≈q)

    ≈ₙₑₚ-trans : ∀ {G : Graph A n} → Transitive (_≈ₙₑₚ_ {G = G})
    ≈ₙₑₚ-trans (refl ∺ refl) (refl ∺ refl) = refl ∺ refl
    ≈ₙₑₚ-trans (refl ∷ p≈q) (refl ∷ q≈r) = refl ∷ (≈ₙₑₚ-trans p≈q q≈r)

    _≟ₙₑₚ_ : ∀ {G : Graph A n} → Decidable (_≈ₙₑₚ_ {G = G})
    (i ∺ j ∣ _ ∣ _) ≟ₙₑₚ (k ∺ l ∣ _ ∣ _) with i ≟ k | j ≟ l
    ... | no  i≢k | _       = no (λ{(i≡k ∺ _) → i≢k i≡k})
    ... | _       | no  j≢l = no (λ{(_ ∺ j≡l) → j≢l j≡l})
    ... | yes i≡k | yes j≡l = yes (i≡k ∺ j≡l)
    (i ∺ j ∣ _ ∣ _) ≟ₙₑₚ (k ∷ q ∣ _ ∣ _) = no λ()
    (i ∷ p ∣ _ ∣ _) ≟ₙₑₚ (k ∺ l ∣ _ ∣ _) = no λ()
    (i ∷ p ∣ _ ∣ _) ≟ₙₑₚ (k ∷ q ∣ _ ∣ _) with i ≟ k | p ≟ₙₑₚ q
    ... | no  i≢k | _       = no (λ{(i≡k ∷ _) → i≢k i≡k})
    ... | _       | no  p≢q = no (λ{(_ ∷ p≡q) → p≢q p≡q})
    ... | yes i≡k | yes p≡q = yes (i≡k ∷ p≡q)

    ≈ₙₑₚ-isEquivalence : ∀ (G : Graph A n) → IsEquivalence (_≈ₙₑₚ_ {G = G})
    ≈ₙₑₚ-isEquivalence G = record { 
        refl  = ≈ₙₑₚ-refl ; 
        sym   = ≈ₙₑₚ-sym ; 
        trans = ≈ₙₑₚ-trans 
      }

    -- Orderings
 
    ≤ₙₑₚ-refl : ∀ {G : Graph A n} → Reflexive (_≤ₙₑₚ_ {G = G})
    ≤ₙₑₚ-refl {_} {i ∺ j ∣ _ ∣ _} = stopFirst refl ≤-refl
    ≤ₙₑₚ-refl {_} {i ∷ p ∣ _ ∣ _} = stepEqual refl ≤ₙₑₚ-refl

    ≤ₙₑₚ-trans : ∀ {G : Graph A n} → Transitive (_≤ₙₑₚ_ {G = G})
    ≤ₙₑₚ-trans (stopFirst i≡k j≤l) (stopFirst k≡m l≤n) = stopFirst (trans i≡k k≡m) (≤-trans j≤l l≤n)
    ≤ₙₑₚ-trans (stopFirst i≡k j≤l) (stopSecond k<m)    = stopSecond (subst (_< _) (sym i≡k) k<m)
    ≤ₙₑₚ-trans (stopSecond i<k)    (stopFirst k≡m l≤n) = stopSecond (subst (_ <_) k≡m i<k)
    ≤ₙₑₚ-trans (stopSecond i<k)    (stopSecond k<m)    = stopSecond (<-trans i<k k<m)
    ≤ₙₑₚ-trans (stepUnequal i<j)   (stepUnequal j<k)   = stepUnequal (<-trans i<j j<k)
    ≤ₙₑₚ-trans (stepUnequal i<j)   (stepEqual j≡k q≤r) = stepUnequal (subst (_ <_) j≡k i<j)
    ≤ₙₑₚ-trans (stepEqual i≡j p≤q) (stepUnequal j<k)   = stepUnequal (subst (_< _) (sym i≡j) j<k)
    ≤ₙₑₚ-trans (stepEqual i≡j p≤q) (stepEqual j≡k q≤r) = stepEqual (trans i≡j j≡k) (≤ₙₑₚ-trans p≤q q≤r)

    ≤ₙₑₚ-antisym : ∀ {G : Graph A n} → Antisymmetric _≈ₙₑₚ_ (_≤ₙₑₚ_ {G = G})
    ≤ₙₑₚ-antisym (stopFirst i≡k j≤l) (stopFirst _ l≤j)  = i≡k ∺ ≤-antisym j≤l l≤j
    ≤ₙₑₚ-antisym (stopFirst refl _)  (stopSecond k<i)   = contradiction refl (<⇒≢ k<i)
    ≤ₙₑₚ-antisym (stopSecond i<k)    (stopFirst refl _) = contradiction refl (<⇒≢ i<k)
    ≤ₙₑₚ-antisym (stopSecond i<k)    (stopSecond k<i)   = contradiction k<i (<⇒≯ i<k)
    ≤ₙₑₚ-antisym (stepUnequal i<j)   (stepUnequal j<i)  = contradiction i<j (<⇒≯ j<i)
    ≤ₙₑₚ-antisym (stepUnequal i<j)   (stepEqual refl _) = contradiction refl (<⇒≢ i<j)
    ≤ₙₑₚ-antisym (stepEqual refl _)  (stepUnequal j<i)  = contradiction refl (<⇒≢ j<i)
    ≤ₙₑₚ-antisym (stepEqual i≡j p≤q) (stepEqual _ q≤p)  = i≡j ∷ ≤ₙₑₚ-antisym p≤q q≤p


    _≤ₙₑₚ?_ : ∀ {G : Graph A n} → Decidable (_≤ₙₑₚ_ {G = G})
    (i ∺ j ∣ _ ∣ _) ≤ₙₑₚ? (k ∺ l ∣ _ ∣ _) with i <? k | i ≟ k | j ≤? l
    ... | yes i<k | _       | _       = yes (stopSecond i<k)
    ... | no  i≮k | no  i≢k | _       = no (λ{(stopFirst i≡k _) → i≢k i≡k; (stopSecond i<k) → i≮k i<k})
    ... | no  i≮k | _       | no  j≰l = no (λ{(stopFirst _ j≤l) → j≰l j≤l; (stopSecond i<k) → i≮k i<k})
    ... | no  _   | yes i≡k | yes j≤l = yes (stopFirst i≡k j≤l)
    (i ∺ j ∣ _ ∣ _) ≤ₙₑₚ? (k ∷ q ∣ _ ∣ _) = no λ()
    (i ∷ p ∣ _ ∣ _) ≤ₙₑₚ? (k ∺ l ∣ _ ∣ _) = no λ()
    (i ∷ p ∣ _ ∣ _) ≤ₙₑₚ? (k ∷ q ∣ _ ∣ _) with i <? k | i ≟ k | p ≤ₙₑₚ? q
    ... | yes i<k | _       | _       = yes (stepUnequal i<k)
    ... | no  i≮k | no  i≢k | _       = no (λ{(stepUnequal i<k) → i≮k i<k; (stepEqual i≡k _) → i≢k i≡k})
    ... | no  i≮k | _       | no  p≰q = no (λ{(stepUnequal i<k) → i≮k i<k; (stepEqual _ p≤q) → p≰q p≤q})
    ... | no  i≮k | yes i≡k | yes p≤q = yes (stepEqual i≡k p≤q)

    ≤ₙₑₚ-resp-≈ₙₑₚ : ∀ {G : Graph A n} → (_≤ₙₑₚ_ {G = G}) RespectedBy _≈ₙₑₚ_
    ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∺ refl) (refl ∺ refl) (stopFirst refl j≤l) = stopFirst refl j≤l
    ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∺ _)    (refl ∺ _)    (stopSecond i<k)     = stopSecond i<k
    ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∷ _)    (refl ∷ _)    (stepUnequal i<k)    = stepUnequal i<k
    ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∷ p≈q)  (refl ∷ r≈s)  (stepEqual refl p≤r) = stepEqual refl (≤ₙₑₚ-resp-≈ₙₑₚ p≈q r≈s p≤r)
  

    -- Operations

    p≈q⇒|p|≡|q| : ∀ {G : Graph A n} {p q : NonEmptySGPath G} → p ≈ₙₑₚ q → length p ≡ length q
    p≈q⇒|p|≡|q| (_ ∺ _) = refl
    p≈q⇒|p|≡|q| (_ ∷ p≈q) = cong suc (p≈q⇒|p|≡|q| p≈q)

    p≈q⇒p₀≡q₀ : ∀ {G : Graph A n} {p q : NonEmptySGPath G} → p ≈ₙₑₚ q → source p ≡ source q
    p≈q⇒p₀≡q₀ (refl ∺ _) = refl
    p≈q⇒p₀≡q₀ (refl ∷ _) = refl
  
    p≉i∷p : ∀ {G : Graph A n} {p : NonEmptySGPath G} {i i∉p ip∈G} → ¬ (p ≈ₙₑₚ i ∷ p ∣ i∉p ∣ ip∈G) 
    p≉i∷p {p = _ ∺ _ ∣ _ ∣ _} ()
    p≉i∷p {p = _ ∷ _ ∣ _ ∣ _} (_ ∷ p≈i∷p) = p≉i∷p p≈i∷p

    i∉p∧p≈q⇒i∉q : ∀ {G : Graph A n} {p q : NonEmptySGPath G} {k} → k ∉ₙₑₚ p → p ≈ₙₑₚ q → k ∉ₙₑₚ q
    i∉p∧p≈q⇒i∉q (notThere k≢i k≢j) (refl ∺ refl) = notThere k≢i k≢j
    i∉p∧p≈q⇒i∉q (notHere  k≢i k∉p) (refl ∷ p≈q)  = notHere  k≢i (i∉p∧p≈q⇒i∉q k∉p p≈q)


    ------------
    -- SPaths --
    ------------

    -- Equality
  
    ≈ₚ-refl : ∀ {G : Graph A n} → Reflexive (_≈ₚ_ {G = G})
    ≈ₚ-refl {_} {[]}    = []
    ≈ₚ-refl {_} {[ _ ]} = [ ≈ₙₑₚ-refl ]

    ≈ₚ-sym : ∀ {G : Graph A n} → Symmetric (_≈ₚ_ {G = G})
    ≈ₚ-sym [] = []
    ≈ₚ-sym [ p≈q ] = [ ≈ₙₑₚ-sym p≈q ]

    ≈ₚ-trans : ∀ {G : Graph A n} → Transitive (_≈ₚ_ {G = G})
    ≈ₚ-trans [] [] = []
    ≈ₚ-trans [ p≈q ] [ q≈r ] = [ ≈ₙₑₚ-trans p≈q q≈r ]

    _≟ₚ_ : ∀ {G : Graph A n} → Decidable (_≈ₚ_ {G = G})
    []    ≟ₚ []    = yes []
    []    ≟ₚ [ _ ] = no λ()
    [ _ ] ≟ₚ []    = no λ()
    [ p ] ≟ₚ [ q ] with p ≟ₙₑₚ q
    ... | no  p≉q = no (λ{[ p≈q ] → p≉q p≈q})
    ... | yes p≈q = yes [ p≈q ]

    ≈ₚ-isEquivalence : ∀ (G : Graph A n) → IsEquivalence (_≈ₚ_ {G = G})
    ≈ₚ-isEquivalence G = record { 
        refl  = ≈ₚ-refl ; 
        sym   = ≈ₚ-sym ; 
        trans = ≈ₚ-trans 
      }

    p≉q⇒[p]≉[q] : ∀ {G : Graph A n} {p q : NonEmptySGPath G} → ¬ (p ≈ₙₑₚ q) → [ p ] ≉ₚ [ q ]
    p≉q⇒[p]≉[q] p≉q [ p≈q ] = p≉q p≈q



    -- Ordering

    ≤ₚ-refl : ∀ {G : Graph A n} → Reflexive (_≤ₚ_ {G = G})
    ≤ₚ-refl {_} {[]} = stop
    ≤ₚ-refl {_} {[ x ]} = lex refl ≤ₙₑₚ-refl

    ≤ₚ-trans : ∀ {G : Graph A n} → Transitive (_≤ₚ_ {G = G})
    ≤ₚ-trans stop              _                 = stop
    ≤ₚ-trans (len |p|<|q|)     (len |q|<|r|)     = len (<-trans |p|<|q| |q|<|r|)
    ≤ₚ-trans (len |p|<|q|)     (lex |q|≡|r| _)   = len (subst (_ <ℕ_) |q|≡|r| |p|<|q|)
    ≤ₚ-trans (lex |p|≡|q| _)   (len |q|<|r|)     = len (subst (_<ℕ _) (sym |p|≡|q|) |q|<|r|)
    ≤ₚ-trans (lex |p|≡|q| p≤q) (lex |q|≡|r| q≤r) = lex (trans |p|≡|q| |q|≡|r|) (≤ₙₑₚ-trans p≤q q≤r)

    ≤ₚ-antisym : ∀ {G : Graph A n} → Antisymmetric _≈ₚ_ (_≤ₚ_ {G = G})
    ≤ₚ-antisym stop            stop            = []
    ≤ₚ-antisym (len |p|<|q|)   (len |q|<|p|)   = contradiction |p|<|q| (<⇒≯ |q|<|p|)
    ≤ₚ-antisym (len |p|<|q|)   (lex |q|≡|p| _) = contradiction (sym |q|≡|p|) (<⇒≢ |p|<|q|)
    ≤ₚ-antisym (lex |p|≡|q| _) (len |q|<|p|)   = contradiction (sym |p|≡|q|) (<⇒≢ |q|<|p|)
    ≤ₚ-antisym (lex _ p≤q)     (lex _ q≤p)     = [ ≤ₙₑₚ-antisym p≤q q≤p ]

    _≤ₚ?_ : ∀ {G : Graph A n} → Decidable (_≤ₚ_ {G = G})
    []    ≤ₚ? _ = yes stop
    [ _ ] ≤ₚ? [] = no λ()
    [ p ] ≤ₚ? [ q ] with suc (length p) ≤ℕ? length q | length p ≟ℕ length q | p ≤ₙₑₚ? q
    ... | yes |p|<|q| | _           | _       = yes (len |p|<|q|)
    ... | no  |p|≮|q| | no  |p|≢|q| | _       = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex |p|≡|q| _) → |p|≢|q| |p|≡|q|})
    ... | no  |p|≮|q| | _           | no  p≰q = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex _ p≤q) → p≰q p≤q})
    ... | no  _       | yes |p|≡|q| | yes p≤q = yes (lex |p|≡|q| p≤q)

    ≤ₚ-resp-≈ₚ : ∀ {G : Graph A n} → (_≤ₚ_ {G = G}) RespectedBy _≈ₚ_
    ≤ₚ-resp-≈ₚ []      _       stop              = stop
    ≤ₚ-resp-≈ₚ [ p≈q ] [ r≈s ] (len |p|<|q|)     rewrite p≈q⇒|p|≡|q| p≈q | p≈q⇒|p|≡|q| r≈s = len |p|<|q|
    ≤ₚ-resp-≈ₚ [ p≈q ] [ r≈s ] (lex |p|≡|q| p≤q) rewrite p≈q⇒|p|≡|q| p≈q | p≈q⇒|p|≡|q| r≈s = lex |p|≡|q| (≤ₙₑₚ-resp-≈ₙₑₚ p≈q r≈s p≤q)

    ≤ₚ-total : ∀ {G : Graph A n} → Total (_≤ₚ_ {G = G})
    ≤ₚ-total [] _ = inj₁ stop
    ≤ₚ-total _ [] = inj₂ stop
    ≤ₚ-total [ p ] [ q ] with ≤ℕ-cmp (length p) (length q)
    ≤ₚ-total [ _ ] [ _ ] | tri< |p|<|q| _ _ = inj₁ (len |p|<|q|)
    ≤ₚ-total [ _ ] [ _ ] | tri> _ _ |p|<|q| = inj₂ (len |p|<|q|)
    ≤ₚ-total [ i ∺ j ∣ _ ∣ _ ] [ k ∺ l ∣ _ ∣ _ ] | tri≈ _ _ _ with cmp i k | ≤-total j l
    ... | tri< i<k _ _ | _        = inj₁ (lex refl (stopSecond i<k))
    ... | tri> _ _ k<i | _        = inj₂ (lex refl (stopSecond k<i))
    ... | tri≈ _ k≡i _ | inj₁ j≤l = inj₁ (lex refl (stopFirst k≡i j≤l))
    ... | tri≈ _ k≡i _ | inj₂ l≤j = inj₂ (lex refl (stopFirst (sym k≡i) l≤j))
    ≤ₚ-total [ i ∺ j ∣ _ ∣ _ ] [ k ∷ (_ ∷ _ ∣ _ ∣ _) ∣ _ ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∺ j ∣ _ ∣ _ ] [ k ∷ (_ ∺ _ ∣ _ ∣ _) ∣ _ ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∷ (_ ∷ _ ∣ _ ∣ _) ∣ _ ∣ _ ] [ k ∺ l ∣ _ ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∷ (_ ∺ _ ∣ _ ∣ _) ∣ _ ∣ _ ] [ k ∺ l ∣ _ ∣ _ ] | tri≈ _ () _
    ≤ₚ-total [ i ∷ p ∣ _ ∣ _ ] [ k ∷ q ∣ _ ∣ _ ] | tri≈ _ |p|≡|q| _ with cmp i k | ≤ₚ-total [ p ] [ q ]
    ... | tri< i<k _ _ | _        = inj₁ (lex |p|≡|q| (stepUnequal i<k))
    ... | tri> _ _ k<i | _        = inj₂ (lex (sym |p|≡|q|) (stepUnequal k<i))
    ... | tri≈ _ _   _ | inj₁ (len |p|<|q|) = contradiction (suc-injective |p|≡|q|) (<⇒≢ |p|<|q|)
    ... | tri≈ _ i≡k _ | inj₁ (lex _ p≤q) = inj₁ (lex |p|≡|q| (stepEqual i≡k p≤q))
    ... | tri≈ _ i≡k _ | inj₂ (len |q|<|p|) = contradiction (suc-injective (sym |p|≡|q|)) (<⇒≢ |q|<|p|)
    ... | tri≈ _ i≡k _ | inj₂ (lex _ q≤p) = inj₂ (lex (sym |p|≡|q|) (stepEqual (sym i≡k) q≤p))

    i∷p≰p : ∀ {G : Graph A n} {p : NonEmptySGPath G} {i i∉p ip∈G} → [ i ∷ p ∣ i∉p ∣ ip∈G ] ≰ₚ [ p ]
    i∷p≰p (len 1+|p|<|p|)   = contradiction 1+|p|<|p| (m+n≮n 1 _)
    i∷p≰p (lex 1+|p|≡|p| _) = contradiction 1+|p|≡|p| (m+1+n≢n 0 _)


  -- Non-abstract proofs

  NEPₛ : ∀ (G : Graph A n) → Setoid a a
  NEPₛ G = record { 
      Carrier = NonEmptySGPath G ; 
      _≈_ = _≈ₙₑₚ_ ; 
      isEquivalence = ≈ₙₑₚ-isEquivalence G 
    }

  Pₛ : ∀ (G : Graph A n) → Setoid a a
  Pₛ G = record { 
      Carrier = SGPath G ; 
      _≈_ = _≈ₚ_; 
      isEquivalence = ≈ₚ-isEquivalence G 
    }


  weight-resp-≈ₚ : ∀ {G : Graph A n} {b} {B : Set b} (▷ : A → B → B) (i : B) {p q : SGPath G} → p ≈ₚ q → weight ▷ i p ≡ weight ▷ i q
  weight-resp-≈ₚ _▷_ 1# {[]} {[]} _ = refl
  weight-resp-≈ₚ _▷_ 1# {[]} {[ _ ]} ()
  weight-resp-≈ₚ _▷_ 1# {[ _ ]} {[]} ()
  weight-resp-≈ₚ _▷_ 1# {[ _ ∺ _ ∣ _ ∣ _ ]} {[ _ ∷ _ ∣ _ ∣ _ ]} [ () ]
  weight-resp-≈ₚ _▷_ 1# {[ _ ∷ _ ∣ _ ∣ _ ]} {[ _ ∺ _ ∣ _ ∣ _ ]} [ () ]
  weight-resp-≈ₚ _▷_ 1# {[ i ∺ j ∣ _ ∣ (v , Gᵢⱼ≡v) ]} {[ .i ∺ .j ∣ _ ∣ (w , Gᵢⱼ≡w) ]} [ refl ∺ refl ] = 
    cong (_▷ 1#) (just-injective (trans (sym Gᵢⱼ≡v) Gᵢⱼ≡w))
  weight-resp-≈ₚ {G} _▷_ 1# {[ i ∷ p ∣ _ ∣ (v , e≡v) ]} {[ .i ∷ q ∣ _ ∣ (w , e≡w) ]} [ refl ∷ p≈q ] = 
    cong₂ _▷_ 
      (just-injective (trans (trans (sym e≡v) (cong (G i) (p≈q⇒p₀≡q₀ p≈q))) e≡w))
      (weight-resp-≈ₚ _▷_ 1# [ p≈q ])
