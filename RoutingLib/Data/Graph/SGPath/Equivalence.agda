open import Level using () renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst₂)
open import Data.Nat using (suc; _<_)

open import RoutingLib.Data.Graph
open import RoutingLib.Data.Graph.SPath renaming  (_∉ₙₑₚ_ to _∉ₙₑₚˢ_;  _≈ₚ_ to _≈ₚˢ_; _≈ₙₑₚ_ to _≈ₙₑₚˢ_;  _≤ₙₑₚ_ to _≤ₙₑₚˢ_; _≤ₚ_ to _≤ₚˢ_;  _∉ₚ_ to _∉ₚˢ_;  source to sourceˢ;  destination to destinationˢ; length to lengthˢ)
open import RoutingLib.Data.Graph.SGPath renaming (_∉ₙₑₚ_ to _∉ₙₑₚˢᵍ_; _≈ₚ_ to _≈ₚˢᵍ_; _≈ₙₑₚ_ to _≈ₙₑₚˢᵍ_; _≤ₙₑₚ_ to _≤ₙₑₚˢᵍ_; _≤ₚ_ to _≤ₚˢᵍ_; _∉ₚ_ to _∉ₚˢᵍ_; source to sourceˢᵍ; destination to destinationˢᵍ; length to lengthˢᵍ)

module RoutingLib.Data.Graph.SGPath.Equivalence {a n} {A : Set a} where

  infix 4 _≃ₙₑₚ_ _≃ₚ_

  data _≃ₙₑₚ_ {G : Graph A n} : NonEmptySPath n → NonEmptySGPath G → Set lzero where
    _∺_ : ∀ {i j k l i≢j k≢l kl∈G} → i ≡ k → j ≡ l   → (i ∺ j ∣ i≢j) ≃ₙₑₚ (k ∺ l ∣ k≢l ∣ kl∈G)
    _∷_ : ∀ {i j p q i∉p j∉q jq∈G} → i ≡ j → p ≃ₙₑₚ q → (i ∷ p ∣ i∉p) ≃ₙₑₚ (j ∷ q ∣ j∉q ∣ jq∈G)

  data _≃ₚ_ {G : Graph A n} : SPath n → SGPath G → Set lzero where
    []  : [] ≃ₚ []
    [_] : ∀ {p q} → p ≃ₙₑₚ q → [ p ] ≃ₚ [ q ]

  abstract

    -- Preserved properties

    ≃ₙₑₚ-source : ∀ {G : Graph A n} {p} {q : NonEmptySGPath G} → p ≃ₙₑₚ q → sourceˢ p ≡ sourceˢᵍ q
    ≃ₙₑₚ-source (refl ∺ _) = refl
    ≃ₙₑₚ-source (refl ∷ _) = refl 

    ≃ₙₑₚ-destination : ∀ {G : Graph A n} {p} {q : NonEmptySGPath G} → p ≃ₙₑₚ q → destinationˢ p ≡ destinationˢᵍ q
    ≃ₙₑₚ-destination (_ ∺ refl) = refl
    ≃ₙₑₚ-destination (_ ∷ p≃q)  = ≃ₙₑₚ-destination p≃q 

    ≃ₙₑₚ-length : ∀ {G : Graph A n} {p} {q : NonEmptySGPath G} → p ≃ₙₑₚ q → lengthˢ p ≡ lengthˢᵍ q
    ≃ₙₑₚ-length (_ ∺ _)   = refl
    ≃ₙₑₚ-length (_ ∷ p≃q) = cong suc (≃ₙₑₚ-length p≃q)

    ≃ₙₑₚ-∉ˢᵍ : ∀ {G : Graph A n} {i p} → {q : NonEmptySGPath G} → p ≃ₙₑₚ q → i ∉ₙₑₚˢ p → i ∉ₙₑₚˢᵍ q
    ≃ₙₑₚ-∉ˢᵍ (refl ∺ refl) (notThere x y)  = notThere x y
    ≃ₙₑₚ-∉ˢᵍ (refl ∷ p≈q)  (notHere x i∉p) = notHere x (≃ₙₑₚ-∉ˢᵍ p≈q i∉p)

    ≃ₚ-∉ˢᵍ : ∀ {G : Graph A n} {i p} → {q : SGPath G} → p ≃ₚ q → i ∉ₚˢ p → i ∉ₚˢᵍ q
    ≃ₚ-∉ˢᵍ []      _               = notHere
    ≃ₚ-∉ˢᵍ [ p≃q ] (notThere i∉p)  = notThere (≃ₙₑₚ-∉ˢᵍ p≃q i∉p)

    ≃ₙₑₚ-∉ˢ : ∀ {G : Graph A n} {i p} → {q : NonEmptySGPath G} → p ≃ₙₑₚ q → i ∉ₙₑₚˢᵍ q → i ∉ₙₑₚˢ p
    ≃ₙₑₚ-∉ˢ (refl ∺ refl) (notThere x y)  = notThere x y
    ≃ₙₑₚ-∉ˢ (refl ∷ p≈q)  (notHere x i∉p) = notHere x (≃ₙₑₚ-∉ˢ p≈q i∉p)

    ≃ₚ-∉ˢ : ∀ {G : Graph A n} {i p} → {q : SGPath G} → p ≃ₚ q → i ∉ₚˢᵍ q → i ∉ₚˢ p
    ≃ₚ-∉ˢ []      _               = notHere
    ≃ₚ-∉ˢ [ p≃q ] (notThere i∉p)  = notThere (≃ₙₑₚ-∉ˢ p≃q i∉p)
 
    ≃ₙₑₚ-≤ˢᵍ : ∀ {G : Graph A n} {p r} {q s : NonEmptySGPath G} → p ≃ₙₑₚ q → r ≃ₙₑₚ s → p ≤ₙₑₚˢ r → q ≤ₙₑₚˢᵍ s
    ≃ₙₑₚ-≤ˢᵍ (refl ∺ refl) (refl ∺ refl) (stopFirst refl k<l) = stopFirst refl k<l
    ≃ₙₑₚ-≤ˢᵍ (refl ∺ refl) (refl ∺ refl) (stopSecond  i<j)    = stopSecond i<j
    ≃ₙₑₚ-≤ˢᵍ (refl ∷ p≃q)  (refl ∷ r≃s)  (stepUnequal i<j)    = stepUnequal i<j
    ≃ₙₑₚ-≤ˢᵍ (refl ∷ p≃q)  (refl ∷ r≃s)  (stepEqual refl p≤r) = stepEqual refl (≃ₙₑₚ-≤ˢᵍ p≃q r≃s p≤r)

    ≃ₚ-≤ˢᵍ : ∀ {G : Graph A n} {p r} {q s : SGPath G} → p ≃ₚ q → r ≃ₚ s → p ≤ₚˢ r → q ≤ₚˢᵍ s
    ≃ₚ-≤ˢᵍ []      _       stop              = stop
    ≃ₚ-≤ˢᵍ [ p≃q ] [ r≃s ] (len |p|<|r|)     = len (subst₂ _<_ (≃ₙₑₚ-length p≃q) (≃ₙₑₚ-length r≃s) |p|<|r|)
    ≃ₚ-≤ˢᵍ [ p≃q ] [ r≃s ] (lex |p|≡|r| p≤r) = lex (subst₂ _≡_ (≃ₙₑₚ-length p≃q) (≃ₙₑₚ-length r≃s) |p|≡|r|) (≃ₙₑₚ-≤ˢᵍ p≃q r≃s p≤r)

    ≃ₙₑₚ-≤ˢ : ∀ {G : Graph A n} {p r} {q s : NonEmptySGPath G} → p ≃ₙₑₚ q → r ≃ₙₑₚ s → q ≤ₙₑₚˢᵍ s → p ≤ₙₑₚˢ r
    ≃ₙₑₚ-≤ˢ (refl ∺ refl) (refl ∺ refl) (stopFirst refl k<l) = stopFirst refl k<l
    ≃ₙₑₚ-≤ˢ (refl ∺ refl) (refl ∺ refl) (stopSecond  i<j)    = stopSecond i<j
    ≃ₙₑₚ-≤ˢ (refl ∷ p≃q)  (refl ∷ r≃s)  (stepUnequal i<j)    = stepUnequal i<j
    ≃ₙₑₚ-≤ˢ (refl ∷ p≃q)  (refl ∷ r≃s)  (stepEqual refl p≤r) = stepEqual refl (≃ₙₑₚ-≤ˢ p≃q r≃s p≤r)

    ≃ₚ-≤ˢ : ∀ {G : Graph A n} {p r} {q s : SGPath G} → p ≃ₚ q → r ≃ₚ s → q ≤ₚˢᵍ s → p ≤ₚˢ r
    ≃ₚ-≤ˢ []      _       stop              = stop
    ≃ₚ-≤ˢ [ p≃q ] [ r≃s ] (len |q|<|s|)     = len (subst₂ _<_ (sym (≃ₙₑₚ-length p≃q)) (sym (≃ₙₑₚ-length r≃s)) |q|<|s|)
    ≃ₚ-≤ˢ [ p≃q ] [ r≃s ] (lex |q|≡|s| q≤s) = lex (subst₂ _≡_ (sym (≃ₙₑₚ-length p≃q)) (sym (≃ₙₑₚ-length r≃s)) |q|≡|s|) (≃ₙₑₚ-≤ˢ p≃q r≃s q≤s)



    -- Transitivity

    ≃ₙₑₚ+≃⇒≈ˢᵍ : ∀ {G : Graph A n} {p q} {r : NonEmptySGPath G} → p ≃ₙₑₚ q → p ≃ₙₑₚ r → q ≈ₙₑₚˢᵍ r
    ≃ₙₑₚ+≃⇒≈ˢᵍ (refl ∺ refl) (refl ∺ refl) = (refl ∺ refl)
    ≃ₙₑₚ+≃⇒≈ˢᵍ (refl ∷ p≃q)  (refl ∷ p≃r)  = refl ∷ ≃ₙₑₚ+≃⇒≈ˢᵍ p≃q p≃r

    ≃ₙₑₚ+≈ˢᵍ⇒≃ : ∀ {G : Graph A n} {p q} {r : NonEmptySGPath G} → p ≃ₙₑₚ q → r ≈ₙₑₚˢᵍ q → p ≃ₙₑₚ r
    ≃ₙₑₚ+≈ˢᵍ⇒≃ (refl ∺ refl) (refl ∺ refl) = (refl ∺ refl)
    ≃ₙₑₚ+≈ˢᵍ⇒≃ (refl ∷ p≃q)  (refl ∷ p≃r)  = refl ∷ ≃ₙₑₚ+≈ˢᵍ⇒≃ p≃q p≃r
  
    ≃ₙₑₚ+≈ˢ⇒≃ : ∀ {G : Graph A n} {p} {q : NonEmptySGPath G} {r} → p ≃ₙₑₚ q → p ≈ₙₑₚˢ r → r ≃ₙₑₚ q
    ≃ₙₑₚ+≈ˢ⇒≃ (refl ∺ refl) (refl ∺ refl) = (refl ∺ refl)
    ≃ₙₑₚ+≈ˢ⇒≃ (refl ∷ p≃q)  (refl ∷ p≃r)  = refl ∷ ≃ₙₑₚ+≈ˢ⇒≃ p≃q p≃r

    ≃ₙₑₚ+≃⇒≈ˢ : ∀ {G : Graph A n} {p} {q : NonEmptySGPath G} {r} → p ≃ₙₑₚ q → r ≃ₙₑₚ q → p ≈ₙₑₚˢ r
    ≃ₙₑₚ+≃⇒≈ˢ (refl ∺ refl) (refl ∺ refl) = (refl ∺ refl)
    ≃ₙₑₚ+≃⇒≈ˢ (refl ∷ p≃q)  (refl ∷ p≃r)  = refl ∷ ≃ₙₑₚ+≃⇒≈ˢ p≃q p≃r



    ≃ₚ+≃⇒≈ˢᵍ : ∀ {G : Graph A n} {p q} {r : SGPath G} → p ≃ₚ q → p ≃ₚ r → q ≈ₚˢᵍ r
    ≃ₚ+≃⇒≈ˢᵍ []      []      = []
    ≃ₚ+≃⇒≈ˢᵍ [ p≃q ] [ p≃r ] = [ ≃ₙₑₚ+≃⇒≈ˢᵍ p≃q p≃r ]

    ≃ₚ+≈ˢᵍ⇒≃ : ∀ {G : Graph A n} {p q} {r : SGPath G} → p ≃ₚ q → r ≈ₚˢᵍ q → p ≃ₚ r
    ≃ₚ+≈ˢᵍ⇒≃ []      []      = []
    ≃ₚ+≈ˢᵍ⇒≃ [ p≃q ] [ p≃r ] = [ ≃ₙₑₚ+≈ˢᵍ⇒≃ p≃q p≃r ]
  
    ≃ₚ+≈ˢ⇒≃ : ∀ {G : Graph A n} {p} {q : SGPath G} {r} → p ≃ₚ q → p ≈ₚˢ r → r ≃ₚ q
    ≃ₚ+≈ˢ⇒≃ []      []      = []
    ≃ₚ+≈ˢ⇒≃ [ p≃q ] [ p≃r ] = [ ≃ₙₑₚ+≈ˢ⇒≃ p≃q p≃r ]

    ≃ₚ+≃⇒≈ˢ : ∀ {G : Graph A n} {p} {q : SGPath G} {r} → p ≃ₚ q → r ≃ₚ q → p ≈ₚˢ r
    ≃ₚ+≃⇒≈ˢ []      []      = []
    ≃ₚ+≃⇒≈ˢ [ p≃q ] [ p≃r ] = [ ≃ₙₑₚ+≃⇒≈ˢ p≃q p≃r ]
