open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Nat using (zero; suc)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Function using (_∘_)
open import Relation.Binary using (Setoid)

open import RoutingLib.Data.Matrix
import RoutingLib.Data.Matrix.Membership as Membership
import RoutingLib.Data.Table as Table
import RoutingLib.Data.Table.Membership.Properties as TableMP

module RoutingLib.Data.Matrix.Membership.Properties where


  module SingleSetoid {a ℓ} (S : Setoid a ℓ) where
  
    open Setoid S renaming (Carrier to A)
    open Membership S

    sel⇒fold[M]∈M : ∀ {_•_ : Op₂ A} → Selective _≈_ _•_ →
                      ∀ (e : A) {m n} (M : Matrix A m n) →
                      fold _•_ e M ≈ e ⊎ fold _•_ e M ∈ M
    sel⇒fold[M]∈M •-sel e {zero}  M = inj₁ refl
    sel⇒fold[M]∈M •-sel e {suc m} M with TableMP.sel⇒foldr[t]∈t S •-sel (fold _ e (M ∘ fsuc)) (M fzero)
    ... | inj₂ (j , f≈M₀ⱼ) = inj₂ (fzero , j , f≈M₀ⱼ)
    ... | inj₁ f≈fM₁ with sel⇒fold[M]∈M •-sel e (M ∘ fsuc)
    ...   | inj₂ (i , j , fM₁≈Mᵢⱼ) = inj₂ (fsuc i , j , trans f≈fM₁ fM₁≈Mᵢⱼ)
    ...   | inj₁ fM₁≈e = inj₁ (trans f≈fM₁ fM₁≈e)
    
    sel⇒fold⁺[M]∈M : ∀ {_•_ : Op₂ A} → Selective _≈_ _•_ →
                       ∀ {m n} (M : Matrix A (suc m) (suc n)) →
                       fold⁺ _•_ M ∈ M
    sel⇒fold⁺[M]∈M {_•_} •-sel {zero}  M = fzero , TableMP.sel⇒foldr⁺[t]∈t S •-sel (M fzero)
    sel⇒fold⁺[M]∈M {_•_} •-sel {suc m} M with •-sel _ (fold⁺ _•_ (M ∘ fsuc)) | TableMP.sel⇒foldr⁺[t]∈t S •-sel (M fzero) | sel⇒fold⁺[M]∈M •-sel (M ∘ fsuc)
    ... | inj₁ t•f≈t | (j , t≈tⱼ) | _ = fzero , j , trans t•f≈t t≈tⱼ
    ... | inj₂ t•f≈f | _          | (i , j , f≈tᵢⱼ) = fsuc i , j , trans t•f≈f f≈tᵢⱼ
    
  open SingleSetoid public




  module DoubleSetoid {a b ℓ₁ ℓ₂} (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where
  

  open DoubleSetoid public


  module TripleSetoid
    {a₁ a₂ a₃ ℓ₁ ℓ₂ ℓ₃}
    (S₁ : Setoid a₁ ℓ₁)
    (S₂ : Setoid a₂ ℓ₂)
    (S₃ : Setoid a₃ ℓ₃)
    where

    open Setoid S₁ using () renaming (Carrier to A₁)
    open Setoid S₂ using () renaming (Carrier to A₂)
    open Setoid S₂ using () renaming (Carrier to A₂)
    
    open Membership S₁ renaming (_∈_ to _∈₁_)
    open Membership S₂ renaming (_∈_ to _∈₂_)
    open Membership S₃ renaming (_∈_ to _∈₃_)
    
    

  open TripleSetoid public


