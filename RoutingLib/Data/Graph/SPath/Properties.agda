open import Relation.Binary using (Decidable; Total; Reflexive; Symmetric; Antisymmetric; Transitive; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (suc) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans)
open import Data.Fin using (Fin; _<_) renaming (suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)

open import RoutingLib.Data.Graph.SPath
open import RoutingLib.Data.Nat.Properties using (<⇒≢; <⇒≯; ≤-refl; m+n≮n; m+1+n≢n; suc-injective) renaming (cmp to ≤ℕ-cmp)
open import RoutingLib.Data.Fin.Properties using (≤-trans; ≤-antisym; ≤-total; _≤?_; _<?_; cmp)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)

module RoutingLib.Data.Graph.SPath.Properties {n} where

  -------------------
  -- NonEmptySPath --
  -------------------

  -- Equality
  
  ≈ₙₑₚ-refl : Reflexive (_≈ₙₑₚ_ {n})
  ≈ₙₑₚ-refl {_ ∺ _ ∣ _} = refl ∺ refl
  ≈ₙₑₚ-refl {_ ∷ _ ∣ _} = refl ∷ ≈ₙₑₚ-refl

  ≈ₙₑₚ-sym : Symmetric (_≈ₙₑₚ_ {n})
  ≈ₙₑₚ-sym (refl ∺ refl) = refl ∺ refl
  ≈ₙₑₚ-sym (refl ∷ p≈q)  = refl ∷ (≈ₙₑₚ-sym p≈q)

  ≈ₙₑₚ-trans : Transitive (_≈ₙₑₚ_ {n})
  ≈ₙₑₚ-trans (refl ∺ refl) (refl ∺ refl) = refl ∺ refl
  ≈ₙₑₚ-trans (refl ∷ p≈q) (refl ∷ q≈r) = refl ∷ (≈ₙₑₚ-trans p≈q q≈r)

  _≟ₙₑₚ_ : Decidable (_≈ₙₑₚ_ {n})
  (i ∺ j ∣ _) ≟ₙₑₚ (k ∺ l ∣ _) with i ≟ k | j ≟ l
  ... | no  i≢k | _       = no (λ{(i≡k ∺ _) → i≢k i≡k})
  ... | _       | no  j≢l = no (λ{(_ ∺ j≡l) → j≢l j≡l})
  ... | yes i≡k | yes j≡l = yes (i≡k ∺ j≡l)
  (i ∺ j ∣ _) ≟ₙₑₚ (k ∷ q ∣ _) = no λ()
  (i ∷ p ∣ _) ≟ₙₑₚ (k ∺ l ∣ _) = no λ()
  (i ∷ p ∣ _) ≟ₙₑₚ (k ∷ q ∣ _) with i ≟ k | p ≟ₙₑₚ q
  ... | no  i≢k | _       = no (λ{(i≡k ∷ _) → i≢k i≡k})
  ... | _       | no  p≢q = no (λ{(_ ∷ p≡q) → p≢q p≡q})
  ... | yes i≡k | yes p≡q = yes (i≡k ∷ p≡q)


  -- Orderings
 
  ≤ₙₑₚ-refl : Reflexive (_≤ₙₑₚ_ {n})
  ≤ₙₑₚ-refl {i ∺ j ∣ _} = stopFirst refl ≤-refl
  ≤ₙₑₚ-refl {i ∷ p ∣ _} = stepEqual refl ≤ₙₑₚ-refl

  ≤ₙₑₚ-trans : Transitive (_≤ₙₑₚ_ {n})
  ≤ₙₑₚ-trans (stopFirst i≡k j≤l) (stopFirst k≡m l≤n) = stopFirst (trans i≡k k≡m) (≤-trans j≤l l≤n)
  ≤ₙₑₚ-trans (stopFirst i≡k j≤l) (stopSecond k<m)    = stopSecond (subst (_< _) (sym i≡k) k<m)
  ≤ₙₑₚ-trans (stopSecond i<k)    (stopFirst k≡m l≤n) = stopSecond (subst (_ <_) k≡m i<k)
  ≤ₙₑₚ-trans (stopSecond i<k)    (stopSecond k<m)    = stopSecond (<-trans i<k k<m)
  ≤ₙₑₚ-trans (stepUnequal i<j)   (stepUnequal j<k)   = stepUnequal (<-trans i<j j<k)
  ≤ₙₑₚ-trans (stepUnequal i<j)   (stepEqual j≡k q≤r) = stepUnequal (subst (_ <_) j≡k i<j)
  ≤ₙₑₚ-trans (stepEqual i≡j p≤q) (stepUnequal j<k)   = stepUnequal (subst (_< _) (sym i≡j) j<k)
  ≤ₙₑₚ-trans (stepEqual i≡j p≤q) (stepEqual j≡k q≤r) = stepEqual (trans i≡j j≡k) (≤ₙₑₚ-trans p≤q q≤r)

  ≤ₙₑₚ-antisym : Antisymmetric _≈ₙₑₚ_ (_≤ₙₑₚ_ {n})
  ≤ₙₑₚ-antisym (stopFirst i≡k j≤l) (stopFirst _ l≤j)  = i≡k ∺ ≤-antisym j≤l l≤j
  ≤ₙₑₚ-antisym (stopFirst refl _)  (stopSecond k<i)   = contradiction refl (<⇒≢ k<i)
  ≤ₙₑₚ-antisym (stopSecond i<k)    (stopFirst refl _) = contradiction refl (<⇒≢ i<k)
  ≤ₙₑₚ-antisym (stopSecond i<k)    (stopSecond k<i)   = contradiction k<i (<⇒≯ i<k)
  ≤ₙₑₚ-antisym (stepUnequal i<j)   (stepUnequal j<i)  = contradiction i<j (<⇒≯ j<i)
  ≤ₙₑₚ-antisym (stepUnequal i<j)   (stepEqual refl _) = contradiction refl (<⇒≢ i<j)
  ≤ₙₑₚ-antisym (stepEqual refl _)  (stepUnequal j<i)  = contradiction refl (<⇒≢ j<i)
  ≤ₙₑₚ-antisym (stepEqual i≡j p≤q) (stepEqual _ q≤p)  = i≡j ∷ ≤ₙₑₚ-antisym p≤q q≤p


  _≤ₙₑₚ?_ : Decidable (_≤ₙₑₚ_ {n})
  (i ∺ j ∣ _) ≤ₙₑₚ? (k ∺ l ∣ _) with i <? k | i ≟ k | j ≤? l
  ... | yes i<k | _       | _       = yes (stopSecond i<k)
  ... | no  i≮k | no  i≢k | _       = no (λ{(stopFirst i≡k _) → i≢k i≡k; (stopSecond i<k) → i≮k i<k})
  ... | no  i≮k | _       | no  j≰l = no (λ{(stopFirst _ j≤l) → j≰l j≤l; (stopSecond i<k) → i≮k i<k})
  ... | no  _   | yes i≡k | yes j≤l = yes (stopFirst i≡k j≤l)
  (i ∺ j ∣ _) ≤ₙₑₚ? (k ∷ q ∣ _) = no λ()
  (i ∷ p ∣ _) ≤ₙₑₚ? (k ∺ l ∣ _) = no λ()
  (i ∷ p ∣ _) ≤ₙₑₚ? (k ∷ q ∣ _) with i <? k | i ≟ k | p ≤ₙₑₚ? q
  ... | yes i<k | _       | _       = yes (stepUnequal i<k)
  ... | no  i≮k | no  i≢k | _       = no (λ{(stepUnequal i<k) → i≮k i<k; (stepEqual i≡k _) → i≢k i≡k})
  ... | no  i≮k | _       | no  p≰q = no (λ{(stepUnequal i<k) → i≮k i<k; (stepEqual _ p≤q) → p≰q p≤q})
  ... | no  i≮k | yes i≡k | yes p≤q = yes (stepEqual i≡k p≤q)

  ≤ₙₑₚ-resp-≈ₙₑₚ : (_≤ₙₑₚ_ {n}) RespectedBy _≈ₙₑₚ_
  ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∺ refl) (refl ∺ refl) (stopFirst refl j≤l) = stopFirst refl j≤l
  ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∺ _)    (refl ∺ _)    (stopSecond i<k)     = stopSecond i<k
  ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∷ _)    (refl ∷ _)    (stepUnequal i<k)    = stepUnequal i<k
  ≤ₙₑₚ-resp-≈ₙₑₚ (refl ∷ p≈q)  (refl ∷ r≈s)  (stepEqual refl p≤r) = stepEqual refl (≤ₙₑₚ-resp-≈ₙₑₚ p≈q r≈s p≤r)
  

  -- Operations

  p≈q⇒|p|≡|q| : ∀ {p q : NonEmptySPath n} → p ≈ₙₑₚ q → length p ≡ length q
  p≈q⇒|p|≡|q| (_ ∺ _) = refl
  p≈q⇒|p|≡|q| (_ ∷ p≈q) = cong suc (p≈q⇒|p|≡|q| p≈q)

  p≈q⇒p₀≡q₀ : ∀ {p q : NonEmptySPath n} → p ≈ₙₑₚ q → source p ≡ source q
  p≈q⇒p₀≡q₀ (refl ∺ _) = refl
  p≈q⇒p₀≡q₀ (refl ∷ _) = refl

  p≉i∷p : ∀ {i : Fin n} {p i∉p} → ¬ (p ≈ₙₑₚ i ∷ p ∣ i∉p) 
  p≉i∷p {p = _ ∺ _ ∣ _} ()
  p≉i∷p {p = _ ∷ _ ∣ _} (_ ∷ p≈i∷p) = p≉i∷p p≈i∷p

  i∉p∧p≈q⇒i∉q : ∀ {p q} {k : Fin n} → k ∉ₙₑₚ p → p ≈ₙₑₚ q → k ∉ₙₑₚ q
  i∉p∧p≈q⇒i∉q (notThere k≢i k≢j) (refl ∺ refl) = notThere k≢i k≢j
  i∉p∧p≈q⇒i∉q (notHere  k≢i k∉p) (refl ∷ p≈q)  = notHere  k≢i (i∉p∧p≈q⇒i∉q k∉p p≈q)

  ------------
  -- SPaths --
  ------------

  -- Equality
  
  ≈ₚ-refl : Reflexive (_≈ₚ_ {n})
  ≈ₚ-refl {[]}    = []
  ≈ₚ-refl {[ _ ]} = [ ≈ₙₑₚ-refl ]

  ≈ₚ-sym : Symmetric (_≈ₚ_ {n})
  ≈ₚ-sym [] = []
  ≈ₚ-sym [ p≈q ] = [ ≈ₙₑₚ-sym p≈q ]

  ≈ₚ-trans : Transitive (_≈ₚ_ {n})
  ≈ₚ-trans [] [] = []
  ≈ₚ-trans [ p≈q ] [ q≈r ] = [ ≈ₙₑₚ-trans p≈q q≈r ]

  _≟ₚ_ : Decidable (_≈ₚ_ {n})
  []    ≟ₚ []    = yes []
  []    ≟ₚ [ _ ] = no λ()
  [ _ ] ≟ₚ []    = no λ()
  [ p ] ≟ₚ [ q ] with p ≟ₙₑₚ q
  ... | no  p≉q = no (λ{[ p≈q ] → p≉q p≈q})
  ... | yes p≈q = yes [ p≈q ]



  -- Ordering

  ≤ₚ-refl : Reflexive (_≤ₚ_ {n})
  ≤ₚ-refl {[]} = stop
  ≤ₚ-refl {[ x ]} = lex refl ≤ₙₑₚ-refl

  ≤ₚ-trans : Transitive (_≤ₚ_ {n})
  ≤ₚ-trans stop              _                 = stop
  ≤ₚ-trans (len |p|<|q|)     (len |q|<|r|)     = len (<-trans |p|<|q| |q|<|r|)
  ≤ₚ-trans (len |p|<|q|)     (lex |q|≡|r| _)   = len (subst (_ <ℕ_) |q|≡|r| |p|<|q|)
  ≤ₚ-trans (lex |p|≡|q| _)   (len |q|<|r|)     = len (subst (_<ℕ _) (sym |p|≡|q|) |q|<|r|)
  ≤ₚ-trans (lex |p|≡|q| p≤q) (lex |q|≡|r| q≤r) = lex (trans |p|≡|q| |q|≡|r|) (≤ₙₑₚ-trans p≤q q≤r)

  ≤ₚ-antisym : Antisymmetric _≈ₚ_ (_≤ₚ_ {n})
  ≤ₚ-antisym stop            stop            = []
  ≤ₚ-antisym (len |p|<|q|)   (len |q|<|p|)   = contradiction |p|<|q| (<⇒≯ |q|<|p|)
  ≤ₚ-antisym (len |p|<|q|)   (lex |q|≡|p| _) = contradiction (sym |q|≡|p|) (<⇒≢ |p|<|q|)
  ≤ₚ-antisym (lex |p|≡|q| _) (len |q|<|p|)   = contradiction (sym |p|≡|q|) (<⇒≢ |q|<|p|)
  ≤ₚ-antisym (lex _ p≤q)     (lex _ q≤p)     = [ ≤ₙₑₚ-antisym p≤q q≤p ]

  _≤ₚ?_ : Decidable (_≤ₚ_ {n})
  []    ≤ₚ? _ = yes stop
  [ _ ] ≤ₚ? [] = no λ()
  [ p ] ≤ₚ? [ q ] with suc (length p) ≤ℕ? length q | length p ≟ℕ length q | p ≤ₙₑₚ? q
  ... | yes |p|<|q| | _           | _       = yes (len |p|<|q|)
  ... | no  |p|≮|q| | no  |p|≢|q| | _       = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex |p|≡|q| _) → |p|≢|q| |p|≡|q|})
  ... | no  |p|≮|q| | _           | no  p≰q = no (λ{(len |p|<|q|) → |p|≮|q| |p|<|q|; (lex _ p≤q) → p≰q p≤q})
  ... | no  _       | yes |p|≡|q| | yes p≤q = yes (lex |p|≡|q| p≤q)

  ≤ₚ-resp-≈ₚ : (_≤ₚ_ {n}) RespectedBy _≈ₚ_
  ≤ₚ-resp-≈ₚ []      _       stop              = stop
  ≤ₚ-resp-≈ₚ [ p≈q ] [ r≈s ] (len |p|<|q|)     rewrite p≈q⇒|p|≡|q| p≈q | p≈q⇒|p|≡|q| r≈s = len |p|<|q|
  ≤ₚ-resp-≈ₚ [ p≈q ] [ r≈s ] (lex |p|≡|q| p≤q) rewrite p≈q⇒|p|≡|q| p≈q | p≈q⇒|p|≡|q| r≈s = lex |p|≡|q| (≤ₙₑₚ-resp-≈ₙₑₚ p≈q r≈s p≤q)

  ≤ₚ-total : Total (_≤ₚ_ {n})
  ≤ₚ-total [] _ = inj₁ stop
  ≤ₚ-total _ [] = inj₂ stop
  ≤ₚ-total [ p ] [ q ] with ≤ℕ-cmp (length p) (length q)
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

  i∷p≰p : ∀ {i : Fin n} {p} {i∉p} → [ i ∷ p ∣ i∉p ] ≰ₚ [ p ]
  i∷p≰p (len 1+|p|<|p|)   = contradiction 1+|p|<|p| (m+n≮n 1 _)
  i∷p≰p (lex 1+|p|≡|p| _) = contradiction 1+|p|≡|p| (m+1+n≢n 0 _)
