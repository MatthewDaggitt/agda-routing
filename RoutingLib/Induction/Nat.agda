open import Data.Nat
open import Data.Nat.Properties
open import Induction.WellFounded using (Well-founded; Acc; acc)
open import Induction.Nat renaming (<-well-founded to <'-well-founded)

module RoutingLib.Induction.Nat where

  <'-acc⇒<-acc : ∀ n → Acc _<′_ n → Acc _<_ n
  <'-acc⇒<-acc zero    _        = acc (λ _ ())
  <'-acc⇒<-acc (suc n) (acc rs) = acc (λ y y≤n → <'-acc⇒<-acc y (rs y (≤⇒≤′ y≤n)))

  <-well-founded : Well-founded _<_
  <-well-founded n = <'-acc⇒<-acc n (<'-well-founded n)
