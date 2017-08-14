open import Relation.Binary using (Setoid)

open import RoutingLib.Data.Matrix
import RoutingLib.Data.Matrix.Membership as Membership

module RoutingLib.Data.Matrix.Membership.Properties where

  module SingleSetoid {a ℓ} (S : Setoid a ℓ) where
  
    open Setoid S renaming (Carrier to A)
    open Membership S

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
