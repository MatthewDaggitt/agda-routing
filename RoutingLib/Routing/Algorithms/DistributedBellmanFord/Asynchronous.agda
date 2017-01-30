open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Vec using (Vec; []; _∷_; allFin; map; foldr)
open import Induction.WellFounded using (Acc; acc)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Asynchronous.Core
open import RoutingLib.Function using (_^_)
open import RoutingLib.Data.Fin.Subset using (_∈?_)
open import RoutingLib.Data.Nat.Properties using (≤-refl)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.Asynchronous
  {a b ℓ n} (rp : RoutingProblem a b ℓ n) (sch : AdmissableSchedule n) where

  open RoutingProblem rp
  open AdmissableSchedule sch

  -- Algorithm

  I : RMatrix
  I i j with j ≟ᶠ i
  ... | yes _ = 1#
  ... | no  _ = 0# 


  δ' : {t : ℕ} → Acc _<_ t → RMatrix → RMatrix
  δ' {zero}  _ X i j = X i j
  δ' {suc t} (acc t-acc) X i j with i ∈? α (suc t)
  ... | no  _ = δ' (t-acc t ≤-refl) X i j
  ... | yes _ = foldr (λ _ → Route) _⊕_ (I i j) (map (λ k → A i k ▷ δ' (t-acc (β (suc t) i k) (causality t i k)) X k j) (allFin n)) 


  δ : ℕ → RMatrix → RMatrix
  δ t = δ' (<-wf t)
    
