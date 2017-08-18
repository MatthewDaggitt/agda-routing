open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Setoid; DecSetoid; Decidable; Total; Reflexive; Symmetric; Antisymmetric; Transitive; _Respects_; IsEquivalence; IsDecEquivalence; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂) renaming (setoid to ≡-setoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (setoid to listSetoid)
open import Data.Nat using (ℕ; suc) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≰⇒>; <⇒≢; <⇒≯; ≤-refl)
open import Data.Fin using (Fin; _<_; _≤?_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cmp; ≤-trans; ≤-antisym; ≤-total; _<?_) renaming (_≟_ to _≟𝔽_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import RoutingLib.Data.Graph using (Graph; ∈-resp-≡ₗ; _∈?_)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)
open import RoutingLib.Data.Maybe.Properties using (just-injective)

module RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties {n} where

  -------------------
  -- Equality

  abstract

    ≈-refl : Reflexive (_≈_ {n})
    ≈-refl {_ ∺ _ ∣ _} = refl ∺ refl
    ≈-refl {_ ∷ _ ∣ _} = refl ∷ ≈-refl

    ≈-sym : Symmetric (_≈_ {n})
    ≈-sym (refl ∺ refl) = refl ∺ refl
    ≈-sym (refl ∷ p≈q)  = refl ∷ (≈-sym p≈q)

    ≈-trans : Transitive (_≈_ {n})
    ≈-trans (refl ∺ refl) (refl ∺ refl) = refl ∺ refl
    ≈-trans (refl ∷ p≈q)  (refl ∷ q≈r)  = refl ∷ (≈-trans p≈q q≈r)

    _≟_ : Decidable (_≈_ {n})
    (i ∺ j ∣ _) ≟ (k ∺ l ∣ _) with i ≟𝔽 k | j ≟𝔽 l
    ... | no  i≢k | _       = no (λ{(i≡k ∺ _) → i≢k i≡k})
    ... | _       | no  j≢l = no (λ{(_ ∺ j≡l) → j≢l j≡l})
    ... | yes i≡k | yes j≡l = yes (i≡k ∺ j≡l)
    (i ∺ j ∣ _) ≟ (k ∷ q ∣ _) = no λ()
    (i ∷ p ∣ _) ≟ (k ∺ l ∣ _) = no λ()
    (i ∷ p ∣ _) ≟ (k ∷ q ∣ _) with i ≟𝔽 k | p ≟ q
    ... | no  i≢k | _       = no (λ{(i≡k ∷ _) → i≢k i≡k})
    ... | _       | no  p≢q = no (λ{(_ ∷ p≡q) → p≢q p≡q})
    ... | yes i≡k | yes p≡q = yes (i≡k ∷ p≡q)

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

  ≈-setoid : Setoid lzero lzero
  ≈-setoid = record 
    { Carrier       = SimplePathⁿᵗ n 
    ; _≈_           = _≈_ 
    ; isEquivalence = ≈-isEquivalence 
    }

  ≈-decSetoid : DecSetoid lzero lzero
  ≈-decSetoid = record
    { Carrier          = SimplePathⁿᵗ n 
    ; _≈_              = _≈_ 
    ; isDecEquivalence = ≈-isDecEquivalence 
    }


  ----------------------
  -- Membership

  abstract

    _∉?_ : Decidable (_∉_ {n})
    k ∉? (i ∺ j ∣ _) with k ≟𝔽 i | k ≟𝔽 j
    ... | yes k≡i | _       = no λ{(notThere k≢i _) → k≢i k≡i}
    ... | _       | yes k≡j = no λ{(notThere _ k≢j) → k≢j k≡j}
    ... | no  k≢i | no  k≢j = yes (notThere k≢i k≢j)
    k ∉? (i ∷ p ∣ _) with k ≟𝔽 i | k ∉? p
    ... | yes i≡j | _       = no λ{(notHere i≢j _) → i≢j i≡j }
    ... | _       | no  i∈p = no λ{(notHere _ i∉p) → i∈p i∉p}
    ... | no  i≢j | yes i∉p = yes (notHere i≢j i∉p)

    ∉-resp-≈ : ∀ {k : Fin n} → (k ∉_) Respects _≈_
    ∉-resp-≈ (refl ∺ refl) (notThere k≢i k≢j) = notThere k≢i k≢j
    ∉-resp-≈ (refl ∷ p≈q)  (notHere  k≢i k∉p) = notHere  k≢i (∉-resp-≈ p≈q k∉p)


    -------------------
    -- Orderings

    ≤ₗₑₓ-refl : Reflexive (_≤ₗₑₓ_ {n})
    ≤ₗₑₓ-refl {i ∺ j ∣ _} = stopFirst refl ≤-refl
    ≤ₗₑₓ-refl {i ∷ p ∣ _} = stepEqual refl ≤ₗₑₓ-refl

    ≤ₗₑₓ-trans : Transitive (_≤ₗₑₓ_ {n})
    ≤ₗₑₓ-trans (stopFirst i≡k j≤l) (stopFirst k≡m l≤n) = stopFirst (trans i≡k k≡m) (≤-trans j≤l l≤n)
    ≤ₗₑₓ-trans (stopFirst i≡k j≤l) (stopSecond k<m)    = stopSecond (subst (_< _) (sym i≡k) k<m)
    ≤ₗₑₓ-trans (stopSecond i<k)    (stopFirst k≡m l≤n) = stopSecond (subst (_ <_) k≡m i<k)
    ≤ₗₑₓ-trans (stopSecond i<k)    (stopSecond k<m)    = stopSecond (<-trans i<k k<m)
    ≤ₗₑₓ-trans (stepUnequal i<j)   (stepUnequal j<k)   = stepUnequal (<-trans i<j j<k)
    ≤ₗₑₓ-trans (stepUnequal i<j)   (stepEqual j≡k q≤r) = stepUnequal (subst (_ <_) j≡k i<j)
    ≤ₗₑₓ-trans (stepEqual i≡j p≤q) (stepUnequal j<k)   = stepUnequal (subst (_< _) (sym i≡j) j<k)
    ≤ₗₑₓ-trans (stepEqual i≡j p≤q) (stepEqual j≡k q≤r) = stepEqual (trans i≡j j≡k) (≤ₗₑₓ-trans p≤q q≤r)

    ≤ₗₑₓ-antisym : Antisymmetric _≈_ (_≤ₗₑₓ_ {n})
    ≤ₗₑₓ-antisym (stopFirst i≡k j≤l) (stopFirst _ l≤j)  = i≡k ∺ ≤-antisym j≤l l≤j
    ≤ₗₑₓ-antisym (stopFirst refl _)  (stopSecond k<i)   = contradiction refl (<⇒≢ k<i)
    ≤ₗₑₓ-antisym (stopSecond i<k)    (stopFirst refl _) = contradiction refl (<⇒≢ i<k)
    ≤ₗₑₓ-antisym (stopSecond i<k)    (stopSecond k<i)   = contradiction k<i (<⇒≯ i<k)
    ≤ₗₑₓ-antisym (stepUnequal i<j)   (stepUnequal j<i)  = contradiction i<j (<⇒≯ j<i)
    ≤ₗₑₓ-antisym (stepUnequal i<j)   (stepEqual refl _) = contradiction refl (<⇒≢ i<j)
    ≤ₗₑₓ-antisym (stepEqual refl _)  (stepUnequal j<i)  = contradiction refl (<⇒≢ j<i)
    ≤ₗₑₓ-antisym (stepEqual i≡j p≤q) (stepEqual _ q≤p)  = i≡j ∷ ≤ₗₑₓ-antisym p≤q q≤p

    _≤ₗₑₓ?_ : Decidable (_≤ₗₑₓ_ {n})
    (i ∺ j ∣ _) ≤ₗₑₓ? (k ∺ l ∣ _) with i <? k | i ≟𝔽 k | j ≤? l
    ... | yes i<k | _       | _       = yes (stopSecond i<k)
    ... | no  i≮k | no  i≢k | _       = no (λ{(stopFirst i≡k _) → i≢k i≡k; (stopSecond i<k) → i≮k i<k})
    ... | no  i≮k | _       | no  j≰l = no (λ{(stopFirst _ j≤l) → j≰l j≤l; (stopSecond i<k) → i≮k i<k})
    ... | no  _   | yes i≡k | yes j≤l = yes (stopFirst i≡k j≤l)
    (i ∺ j ∣ _) ≤ₗₑₓ? (k ∷ q ∣ _) = no λ()
    (i ∷ p ∣ _) ≤ₗₑₓ? (k ∺ l ∣ _) = no λ()
    (i ∷ p ∣ _) ≤ₗₑₓ? (k ∷ q ∣ _) with i <? k | i ≟𝔽 k | p ≤ₗₑₓ? q
    ... | yes i<k | _       | _       = yes (stepUnequal i<k)
    ... | no  i≮k | no  i≢k | _       = no (λ{(stepUnequal i<k) → i≮k i<k; (stepEqual i≡k _) → i≢k i≡k})
    ... | no  i≮k | _       | no  p≰q = no (λ{(stepUnequal i<k) → i≮k i<k; (stepEqual _ p≤q) → p≰q p≤q})
    ... | no  i≮k | yes i≡k | yes p≤q = yes (stepEqual i≡k p≤q)

    ≤ₗₑₓ-resp-≈ : (_≤ₗₑₓ_ {n}) RespectedBy _≈_
    ≤ₗₑₓ-resp-≈ (refl ∺ refl) (refl ∺ refl) (stopFirst refl j≤l) = stopFirst refl j≤l
    ≤ₗₑₓ-resp-≈ (refl ∺ _)    (refl ∺ _)    (stopSecond i<k)     = stopSecond i<k
    ≤ₗₑₓ-resp-≈ (refl ∷ _)    (refl ∷ _)    (stepUnequal i<k)    = stepUnequal i<k
    ≤ₗₑₓ-resp-≈ (refl ∷ p≈q)  (refl ∷ r≈s)  (stepEqual refl p≤r) = stepEqual refl (≤ₗₑₓ-resp-≈ p≈q r≈s p≤r)

    --------------------
    -- Operations

    p≈q⇒|p|≡|q| : ∀ {p q : SimplePathⁿᵗ n} → p ≈ q → length p ≡ length q
    p≈q⇒|p|≡|q| (_ ∺ _) = refl
    p≈q⇒|p|≡|q| (_ ∷ p≈q) = cong suc (p≈q⇒|p|≡|q| p≈q)

    p≈q⇒p₀≡q₀ : ∀ {p q : SimplePathⁿᵗ n} → p ≈ q → source p ≡ source q
    p≈q⇒p₀≡q₀ (refl ∺ _) = refl
    p≈q⇒p₀≡q₀ (refl ∷ _) = refl

    p₀≢q₀⇨p≉q : ∀ {p q : SimplePathⁿᵗ n} → source p ≢ source q → p ≉ q
    p₀≢q₀⇨p≉q i≢j (i≡j ∺ _) = i≢j i≡j
    p₀≢q₀⇨p≉q i≢j (i≡j ∷ _) = i≢j i≡j

    p≉i∷p : ∀ {i : Fin n} {p i∉p} → ¬ (p ≈ i ∷ p ∣ i∉p)
    p≉i∷p {p = _ ∺ _ ∣ _} ()
    p≉i∷p {p = _ ∷ _ ∣ _} (_ ∷ p≈i∷p) = p≉i∷p p≈i∷p


    lookup-∈ : (p : SimplePathⁿᵗ n) → ∀ i {k} → p ⟦ i ⟧ ≡ k → ¬ (k ∉ p)
    lookup-∈ (i ∺ j ∣ _) fzero            refl (notThere i≢i _) = i≢i refl
    lookup-∈ (i ∺ j ∣ _) (fsuc fzero)     refl (notThere _ j≢j) = j≢j refl
    lookup-∈ (i ∺ j ∣ _) (fsuc (fsuc ()))
    lookup-∈ (i ∷ p ∣ _) fzero            refl (notHere i≢i _)  = i≢i refl
    lookup-∈ (i ∷ p ∣ _) (fsuc k)         pᵢ≡k  (notHere _ i∉p)  = lookup-∈ p k pᵢ≡k i∉p

    lookup! : ∀ (p : SimplePathⁿᵗ n) {k l} → k ≢ l → p ⟦ k ⟧ ≢ p ⟦ l ⟧
    lookup! _             {fzero}          {fzero}          0≢0 _ = 0≢0 refl
    lookup! (i ∺ j ∣ i≢j) {fzero}          {fsuc fzero}     _     = i≢j
    lookup! (i ∺ j ∣ i≢j) {fsuc fzero}     {fzero}          _     = i≢j ∘ sym
    lookup! (i ∺ j ∣ x)   {_}              {fsuc (fsuc ())} _
    lookup! (i ∺ j ∣ x)   {fsuc (fsuc ())} {_}
    lookup! (i ∺ j ∣ x)   {fsuc fzero}     {fsuc fzero}     1≢1 _ = 1≢1 refl
    lookup! (i ∷ p ∣ i∉p) {fzero}          {fsuc j}         i≢j i≡pⱼ = contradiction i∉p (lookup-∈ p j (sym i≡pⱼ))
    lookup! (i ∷ p ∣ i∉p) {fsuc k}         {fzero}          i≢j pₖ≡i = contradiction i∉p (lookup-∈ p k pₖ≡i)
    lookup! (i ∷ p ∣ x)   {fsuc k}         {fsuc l}         k+1≢l+1 pₖ≡pₗ = lookup! p (k+1≢l+1 ∘ cong fsuc) pₖ≡pₗ

    |p|<n : ∀ (p : SimplePathⁿᵗ n) → length p <ℕ n
    |p|<n p with suc (length p) ≤ℕ? n
    ... | yes |p|<n = |p|<n
    ... | no  |p|≮n with pigeonhole (≰⇒> |p|≮n) (p ⟦_⟧)
    ...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookup! p i≢j)
  

    ---------------------
    -- Graph membership

    ∈𝔾-resp-≈ : ∀ {a} {A : Set a} {G : Graph A n} → (_∈𝔾 G) Respects _≈_
    ∈𝔾-resp-≈ (refl ∺ refl) (edge-∺ ij∈G)     = edge-∺ ij∈G
    ∈𝔾-resp-≈ {G = G} {i ∷ _ ∣ _} (refl ∷ p≈q)  (edge-∷ ip∈G p∈G) = edge-∷ (∈-resp-≡ₗ {i = i} {G = G} ip∈G (p≈q⇒p₀≡q₀ p≈q)) (∈𝔾-resp-≈ p≈q p∈G)

    ∉𝔾-resp-≈ : ∀ {a} {A : Set a} {G : Graph A n} → (_∉𝔾 G) Respects _≈_
    ∉𝔾-resp-≈ p≈q p∉G q∈G = contradiction (∈𝔾-resp-≈ (≈-sym p≈q) q∈G) p∉G
    
    _∈𝔾?_ : ∀ {a} {A : Set a} → Decidable (_∈𝔾_ {n = n} {A})
    (i ∺ j ∣ x) ∈𝔾? G with (i , j) ∈? G
    ... | yes ij∈G = yes (edge-∺ ij∈G)
    ... | no  ij∉G = no (λ {(edge-∺ ij∈G) → ij∉G ij∈G})
    (i ∷ p ∣ x) ∈𝔾? G with (i , source p) ∈? G | p ∈𝔾? G
    ... | yes ip₀∈G | yes p∈G = yes (edge-∷ ip₀∈G p∈G)
    ... | no  ip₀∉G | _       = no (λ {(edge-∷ ip₀∈G _) → ip₀∉G ip₀∈G})
    ... | _         | no  p∉G = no (λ {(edge-∷ _ p∈G) → p∉G p∈G})
    
    weight-cong : ∀ {a b} {A : Set a} {B : Set b} _▷_ (1# : B) {p q : SimplePathⁿᵗ n} {G : Graph A n} → p ≈ q → (p∈G : p ∈𝔾 G) (q∈G : q ∈𝔾 G) → weight _▷_ 1# p∈G ≡ weight _▷_ 1# q∈G
    weight-cong _▷_ 1# {G = G} (refl ∺ refl) (edge-∺ (v , Gᵢⱼ≈v))     (edge-∺ (w , Gᵢⱼ≈w))     = cong (_▷ 1#) (just-injective (trans (sym Gᵢⱼ≈v) Gᵢⱼ≈w))
    weight-cong _▷_ 1# {G = G} (refl ∷ p≈q)  (edge-∷ (v , Gᵢⱼ≈v) p∈G) (edge-∷ (w , Gᵢⱼ≈w) q∈G) = cong₂ _▷_ (just-injective (trans (sym Gᵢⱼ≈v) (trans (cong (G _) (p≈q⇒p₀≡q₀ p≈q)) Gᵢⱼ≈w))) (weight-cong _▷_ 1# p≈q p∈G q∈G)
