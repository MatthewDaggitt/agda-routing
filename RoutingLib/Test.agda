open import Data.Nat using (ℕ; zero; suc)
open import Induction.WellFounded using (Acc; acc; Well-founded)
open import Relation.Binary using (Rel)


module RoutingLib.Test {a ℓ} {A : Set a} where

  postulate _<_ : Rel A ℓ

  postulate <-wf : Well-founded _<_



  height : ∀ {x} → Acc _<_ x → ℕ
  height (acc rs) = {!!}
