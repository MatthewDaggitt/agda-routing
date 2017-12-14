open import Data.Nat using (ℕ; zero)
--open import Relation.Binary.PropositionalEquality using (_≡_)
--open import Level using (_⊔_)  renaming (suc to lsuc)

module RoutingLib.Routing.BellmanFord.PathsConvergence2.Test where

{-
  record R a b : Set (lsuc a ⊔ b) where
    field
      f : Set a

  module Inner {a b} {r : R a b} where
    
    r2 : R a (lsuc b)
    r2 = record { f = R.f r}

    module Inner2 {a b} (r : R a b) where
      postulate n : ℕ
    open Inner2 r2
    
    test : n ≡ n
    test with zero
    ... | c = {!!}
-}

  test : ℕ
  test = {!zero!}
