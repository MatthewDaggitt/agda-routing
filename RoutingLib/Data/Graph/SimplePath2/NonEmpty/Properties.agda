open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Setoid; DecSetoid; Decidable; Total; Reflexive; Symmetric; Antisymmetric; Transitive; _Respects_; IsEquivalence; IsDecEquivalence; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂) renaming (setoid to ≡-setoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (setoid to listSetoid)
open import Data.Nat using (ℕ; suc) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≰⇒>; <⇒≢; <⇒≯; ≤-refl; 1+n≰n; _<?_; ≰⇒≥)
open import Data.Fin using (Fin; _<_; _≤?_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cmp; ≤-trans; ≤-antisym; ≤-total) renaming (_≟_ to _≟𝔽_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Function using (_∘_)

open import RoutingLib.Data.Graph using (Graph; ∈-resp-≡ₗ; _∈?_)
open import RoutingLib.Data.Graph.SimplePath2.NonEmpty
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)
open import RoutingLib.Data.Maybe.Properties using (just-injective)

module RoutingLib.Data.Graph.SimplePath2.NonEmpty.Properties {n} where

  private
    _≟𝔼_ : Decidable {A = Fin n × Fin n} _≡_
    _≟𝔼_ = _≟𝔽_ ×-≟ _≟𝔽_
    
  -------------------
  -- Equality

  abstract

    ≈-refl : Reflexive (_≈_ {n})
    ≈-refl {[]}            = []
    ≈-refl {_ ∷ _ ∣ _ ∣ _} = refl ∷ ≈-refl

    ≈-sym : Symmetric (_≈_ {n})
    ≈-sym []           = []
    ≈-sym (refl ∷ p≈q) = refl ∷ (≈-sym p≈q)

    ≈-trans : Transitive (_≈_ {n})
    ≈-trans []            []           = []
    ≈-trans (refl ∷ p≈q)  (refl ∷ q≈r) = refl ∷ (≈-trans p≈q q≈r)
{-
    _≟_ : Decidable (_≈_ {n})
    [] ≟ [] = yes []
    [] ≟ (k ∷ q ∣ _ ∣ _) = no λ()
    (i ∷ p ∣ _ ∣ _) ≟ [] = no λ()
    (i ∷ p ∣ _ ∣ _) ≟ (k ∷ q ∣ _ ∣ _) with i ≟𝔼 k | p ≟ q
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

    ⇿-resp-≈ : ∀ {e : Fin n × Fin n} → (e ⇿_) Respects _≈_
    ⇿-resp-≈ []           (start i≢j)    = start i≢j
    ⇿-resp-≈ (refl ∷ p≈q) (continue i≢j) = continue i≢j
-}  
    ij⇿p⇒i≢j : ∀ {n} {i j : Fin n} {p} → (i , j) ⇿ p → i ≢ j
    ij⇿p⇒i≢j (start    i≢j) = i≢j
    ij⇿p⇒i≢j (continue i≢j) = i≢j
{-
  ----------------------
  -- Membership
  

    _∉?_ : Decidable (_∉_ {n})
    k ∉? [] = yes notThere
    k ∉? ((i , j) ∷ p ∣ _ ∣ _) with k ≟𝔽 i | k ≟𝔽 j | k ∉? p
    ... | yes k≡i | _       | _       = no  λ{(notHere k≢i _ _) → k≢i k≡i }
    ... | _       | yes k≡j | _       = no  λ{(notHere _ k≢j _) → k≢j k≡j }
    ... | _       | _       | no  i∈p = no  λ{(notHere _ _ i∉p) → i∈p i∉p}
    ... | no  k≢i | no  k≢j | yes i∉p = yes (notHere k≢i k≢j i∉p)

    ∉-resp-≈ : ∀ {k : Fin n} → (k ∉_) Respects _≈_
    ∉-resp-≈ []            notThere             = notThere
    ∉-resp-≈ (refl ∷ p≈q) (notHere k≢i k≢j k∉p) = notHere k≢i k≢j (∉-resp-≈ p≈q k∉p)
    
    -------------------
    -- Orderings
    
    ≤ₗₑₓ-refl : Reflexive (_≤ₗₑₓ_ {n})
    ≤ₗₑₓ-refl {[]}            = stop
    ≤ₗₑₓ-refl {i ∷ p ∣ _ ∣ _} = step refl refl ≤ₗₑₓ-refl

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

    ≤ₗₑₓ-antisym : Antisymmetric _≈_ (_≤ₗₑₓ_ {n})
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
    ((i , j) ∷ p ∣ _ ∣ _) ≤ₗₑₓ? ((k , l) ∷ q ∣ _ ∣ _) with cmp i k | cmp j l |  p ≤ₗₑₓ? q
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

    ≤ₗₑₓ-resp-≈ : (_≤ₗₑₓ_ {n}) RespectedBy _≈_
    ≤ₗₑₓ-resp-≈ []            _             stop                 = stop
    ≤ₗₑₓ-resp-≈ (refl ∷ _)    (refl ∷ _)    (here₁ i<k)          = here₁ i<k
    ≤ₗₑₓ-resp-≈ (refl ∷ _)    (refl ∷ _)    (here₂ i≡k j<l)      = here₂ i≡k j<l
    ≤ₗₑₓ-resp-≈ (refl ∷ p≈q)  (refl ∷ r≈s)  (step refl refl p≤r) = step refl refl (≤ₗₑₓ-resp-≈ p≈q r≈s p≤r)
    
    --------------------
    -- Operations

    p≈q⇒|p|≡|q| : ∀ {p q : SimplePathⁿᵗ n} → p ≈ q → length p ≡ length q
    p≈q⇒|p|≡|q| []        = refl
    p≈q⇒|p|≡|q| (_ ∷ p≈q) = cong suc (p≈q⇒|p|≡|q| p≈q)

    p≉i∷p : ∀ {e} {p : SimplePathⁿᵗ n} {e⇿p e∉p} → ¬ (p ≈ e ∷ p ∣ e⇿p ∣ e∉p)
    p≉i∷p {p = []}            ()
    p≉i∷p {p = _ ∷ _ ∣ _ ∣ _} (_ ∷ p≈i∷p) = p≉i∷p p≈i∷p
-}

    ∉-lookup : ∀ {p : SimplePathⁿᵗ n} (p⁺ : NonEmpty p) →
               ∀ e → e ∉ p → ∀ i → e ≢ lookupᵥ p⁺ i
    ∉-lookup = {!!}

    lookup! : ∀ {p : SimplePathⁿᵗ n} (p⁺ : NonEmpty p) → ∀ k l → k ≢ l → lookupᵥ p⁺ k ≢ lookupᵥ p⁺ l
    lookup! (nonEmpty e p e⇿p e∉p)               fzero           fzero           0≢0 = contradiction refl 0≢0
    lookup! (nonEmpty e p e⇿p e∉p)               fzero           (fsuc fzero)    _   = ij⇿p⇒i≢j e⇿p ∘ sym
    lookup! (nonEmpty e [] e⇿p e∉p)              fzero           (fsuc (fsuc ()))
    lookup! (nonEmpty e (_ ∷ _ ∣ _ ∣ _) e⇿p e∉p) fzero           (fsuc (fsuc l)) _   = ∉-lookup {!!} (proj₂ e) {!!} l
    lookup! (nonEmpty e p e⇿p e∉p)               (fsuc fzero)    fzero           _   = ij⇿p⇒i≢j e⇿p
    lookup! (nonEmpty e [] e⇿p e∉p)              (fsuc (fsuc ())) _      
    lookup! (nonEmpty e (_ ∷ _ ∣ _ ∣ _) e⇿p e∉p) (fsuc (fsuc k)) fzero           _   = {!!}
    lookup! (nonEmpty e p e⇿p e∉p)               (fsuc fzero)    (fsuc fzero)    1≢1 = contradiction refl 1≢1
    lookup! (nonEmpty e p e⇿p e∉p)               (fsuc fzero)    (fsuc (fsuc l)) _   = {!!}
    lookup! (nonEmpty e p e⇿p e∉p)               (fsuc (fsuc k)) (fsuc fzero)    _   = {!!}
    lookup! (nonEmpty e (_ ∷ _ ∣ _ ∣ _) e⇿p e∉p) (fsuc (fsuc k)) (fsuc (fsuc l)) k≢l = lookup! (nonEmpty _ _ _ _) (fsuc k) (fsuc l) (k≢l ∘ cong fsuc)

    |p|<n : ∀ {p : SimplePathⁿᵗ n} → NonEmpty p → length p <ℕ n
    |p|<n q@(nonEmpty e p e⇿p e∉p) with suc (length p) <? n
    ... | yes |q|<n = |q|<n
    ... | no  |q|≮n with pigeonhole (≰⇒> |q|≮n) (lookupᵥ q)
    ...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookup! q i j i≢j)
