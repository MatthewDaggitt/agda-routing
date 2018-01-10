-- imports
open import Computation
  using (Computation; ACO)
open import Data.Nat
  using (ℕ; _+_; zero; suc)
open import Data.Fin
  using (Fin)
open import Relation.Binary
  using (Setoid; IsPreorder)
open import Data.Product
  using (_×_; ∃; _,_; proj₁)
open import Relation.Unary
  using (_∈_; ｛_｝)
open import Relation.Binary.PropositionalEquality
  using (subst; cong₂; _≡_; cong) renaming (sym to ≡sym; trans to ≡trans)
open import Data.Nat.Properties
  using (+-suc; +-identityˡ; +-comm)

module Computation.Properties {a}{ℓ}{n : ℕ}{S : Fin n → Setoid a ℓ}{c : Computation S}(aco : ACO c) where
  open Computation.Computation c
  open Computation.ACO aco
  open Setoid
  open IsPreorder


{-
  ξ-in : ∀ K (x : (j : Fin n) → Carrier (S j)) → (∀ i → x i ∈ D i (M + K)) →
       (∀ i → (_≈_ (S i) (x i) (ξ i)))
  ξ-in K x p i with D-finish i K
  ... | _ , x≡ξ = x≡ξ (p i)

  ξ-fixed-point : ∀ i → (_≈_ (S i)) (f ξ i) (ξ i)
  ξ-fixed-point = ξ-in 1 (f ξ) λ i →
                subst (f ξ i ∈_) (cong (D i) (≡sym (+-suc M 0)))
                (c-monotone (M + 0) (λ j → proj₁ (D-finish j 0)) i)


  z : ∀ K i {x y} → (_≈_ (S i)) x y → x ∈ D i K → y ∈ D i K
  z K i x≡y x∈DK = {!x∈DK!}

  fixed-monotone : ∀ K K₁ → (x : ∀ i → Carrier (S i)) →
                 (∀ i → (_≈_ (S i)) (f x i) (x i)) →
                 (∀ i → x i ∈ D i K) →
                 (∀ i → x i ∈ D i (K₁ + K))
  fixed-monotone K zero x fx≡x x∈DK =  λ i → subst ((x i) ∈_) (cong (D i)
                 (+-identityˡ K)) (x∈DK i)
  fixed-monotone K (suc K₁) x fx≡x x∈DK = λ i → subst ((x i) ∈_) (cong (D i) (+-suc K₁ K))
                 (fixed-monotone (suc K) K₁ x fx≡x
                 (λ j → z (suc K) j (fx≡x j) (c-monotone K x∈DK j))
                 i)
                 -- (λ j → subst-f j (_∈ (D j (suc K))) (fx≡x j) (c-monotone K x∈DK j)) i)
                   
  -- Proposition 2
  prop2-i : ∀ i → (_≈_ (S i)) (f ξ i) (ξ i)
  prop2-i = ξ-fixed-point

  prop2-ii : ∀ x → (∃ λ K → ∀ i → x i ∈ D i K) × (∀ i → (_≈_ (S i)) (f x i) (x i)) →
           (∀ i → (_≈_ (S i)) (x i) (ξ i))
  prop2-ii x ((K , x∈DK) , fx≡x) = ξ-in K x (fixed-monotone K M x fx≡x x∈DK)
                                                                        
-}
