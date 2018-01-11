open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_)
open import Relation.Binary using (DecSetoid; Setoid; Rel; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred) renaming (_∈_ to _∈ᵤ_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.Table using (Table)

import RoutingLib.Data.Table.Relation.Equality as TableEquality

module RoutingLib.Asynchronous where

  -----------------------
  -- Parallel function --
  -----------------------
  -- An operation σ that can be decomposed and carried out on n separate processors 
  record Parallelisation {a ℓ n} (S : Table (Setoid a ℓ) n) : Set (lsuc a) where

    M : Set a
    M = ∀ i → Setoid.Carrier (S i)

    --open TableEquality S renaming (_≈ₜ_ to _≈ₘ_) public
    
    field
      -- The update functions: "σ X i" is the result of processor i activating on state X 
      f      : M → M
      --σ-cong : σ Preserves _≈ₘ_ ⟶ _≈ₘ_

    module _ {i : Fin n} where
      open Setoid (S i)
           renaming 
           ( _≈_       to _≈ᵢ_
           ; reflexive to ≈ᵢ-reflexive
           ; refl      to ≈ᵢ-refl
           ; sym       to ≈ᵢ-sym
           ; trans     to ≈ᵢ-trans
           ) public
           
    MPred : Set (lsuc a)
    MPred = ∀ i → Pred (Setoid.Carrier (S i)) a

    MRel : Set (lsuc a)
    MRel = ∀ {i} → Rel (Setoid.Carrier (S i)) a

    _∈_ : M → MPred → Set a
    t ∈ P = ∀ i → t i ∈ᵤ P i

    _∉_ : M → MPred → Set a
    t ∉ P = ¬ (t ∈ P)

    _⊆_ : MPred → MPred → Set a
    P ⊆ Q = ∀ t → t ∈ P → t ∈ Q 

    _⊂_ : MPred → MPred → Set a
    P ⊂ Q = P ⊆ Q × ∃ λ t → t ∈ Q × ¬ (t ∈ P)

    _≈_ : Rel M ℓ
    s ≈ t = ∀ i → s i ≈ᵢ t i

    _≉_ : Rel M ℓ
    s ≉ t = ¬ (s ≈ t)
    
    ｛_｝ : M → Pred M ℓ
    ｛ t ｝ = t ≈_

    Singleton-t : M → Pred MPred (a ⊔ ℓ)
    Singleton-t t P = t ∈ P × ∀ s → s ∈ P → t ≈ s

    module _ (𝕤 : Schedule n) where

      open Schedule 𝕤

      async-iter : ∀ {t} → Acc _<_ t → M → M
      async-iter {zero} _ x₀ i = x₀ i
      async-iter {suc t} (acc rs) x₀ i with i ∈? α (suc t)
      ... | yes _ = f (λ j → async-iter (rs (β (suc t) i j) (s≤s (causality t i j)))
                x₀ j) i
      ... | no  _ = async-iter (rs t ≤-refl) x₀ i

     -- β (suc t) i j < suc t
     -- causality :

 
{-
    module _ {i : Fin n} where
      open Setoid (S i)
           renaming 
           ( _≈_       to _≈ᵢ_
           ; reflexive to ≈ᵢ-reflexive
           ; refl      to ≈ᵢ-refl
           ; sym       to ≈ᵢ-sym
           ; trans     to ≈ᵢ-trans
           ) public
           -}
{-
    -- The asynchronous state function
    δ' : Schedule n → ∀ {t} → Acc _<_ t → M → M
    δ' 𝕤 {zero}  _           X = X
    δ' 𝕤 {suc t} (acc tAcc) X i with i ∈? α 𝕤 (suc t)
    ... | no  i∉αₜ = δ' 𝕤 (tAcc t ≤-refl) X i
    ... | yes i∈αₜ = σ (λ k → δ' 𝕤 (tAcc (β 𝕤 (suc t) i k) (causality 𝕤 t i k)) X k) i

    δ : Schedule n → ℕ → M → M
    δ 𝕤 t = δ' 𝕤 (<-wf t)

    -- The synchronous state function
    σ^ : ℕ → M → M
    σ^ = δ (𝕤-sync n)
-}

  -----------
  -- Other --
  -----------

{-
  -- A record encapsulating the idea that p is a well behaved parallelisation
  record IsAsynchronouslySafe {a ℓ n} {S : Setoid a ℓ} (p : Parallelisation S n) : Set (lsuc (a ⊔ ℓ)) where
  
    open Parallelisation p
    
    field
      m*         : M
      m*-reached : ∀ 𝕤 X → ∃ λ tᶜ → ∀ t → δ 𝕤 (tᶜ + t) X ≈ₘ m*
-}
