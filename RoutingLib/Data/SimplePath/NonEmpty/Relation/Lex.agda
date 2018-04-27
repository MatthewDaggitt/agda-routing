open import Data.Fin using (_<_)
open import Data.Fin.Properties using (<-trans; cmp)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<⇒≯; 1+n≰n)
open import Data.Product using (_,_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.Lattice using (Minimum)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.SimplePath.NonEmpty
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality

module RoutingLib.Data.SimplePath.NonEmpty.Relation.Lex {n : ℕ} where

  -- Lexicographic order
  infix 4 _≤ₗₑₓ_
  data _≤ₗₑₓ_  : Rel (SimplePathⁿᵗ n) ℓ₀ where
    stop  : ∀ {p} → [] ≤ₗₑₓ p
    here₁ : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
            i < k → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q
    here₂ : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
            i ≡ k → j < l → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q
    step  : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
            i ≡ k → j ≡ l → p ≤ₗₑₓ q  → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q
            
  postulate _<ₗₑₓ_ : Rel (SimplePathⁿᵗ n) ℓ₀


  -- Properties

  abstract
  
    ≤ₗₑₓ-refl : Reflexive _≤ₗₑₓ_
    ≤ₗₑₓ-refl {[]}            = stop
    ≤ₗₑₓ-refl {i ∷ p ∣ _ ∣ _} = step refl refl ≤ₗₑₓ-refl

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

    _≤ₗₑₓ?_ : Decidable _≤ₗₑₓ_
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
    
  postulate <ₗₑₓ-cmp : Trichotomous _≈ₚ_ _<ₗₑₓ_

  postulate <ₗₑₓ-trans : Transitive _<ₗₑₓ_

  postulate <ₗₑₓ-asym : Asymmetric _<ₗₑₓ_
  
  postulate <ₗₑₓ-irrefl : Irreflexive _≈ₚ_ _<ₗₑₓ_

  postulate <ₗₑₓ-minimum : Minimum _<ₗₑₓ_ []

  postulate <ₗₑₓ-respˡ-≈ₚ : {p : SimplePathⁿᵗ n} → (p <ₗₑₓ_) Respects _≈ₚ_

  postulate <ₗₑₓ-respʳ-≈ₚ : {p : SimplePathⁿᵗ n} → (_<ₗₑₓ p) Respects _≈ₚ_

  postulate <ₗₑₓ-resp-≈ₚ : _<ₗₑₓ_ Respects₂ _≈ₚ_

