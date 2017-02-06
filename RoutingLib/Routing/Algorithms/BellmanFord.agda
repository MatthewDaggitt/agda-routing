open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Vec using (Vec; []; _∷_; tabulate; foldr)
open import Induction.WellFounded using (Acc; acc)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Asynchronous using (Parallelisation) renaming (δ^ to δ^'; σ^ to σ^')
open import RoutingLib.Asynchronous.Schedule using (Schedule)
open import RoutingLib.Function using (_^_)
open import RoutingLib.Data.Nat.Properties using (≤-refl)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)

module RoutingLib.Routing.Algorithms.BellmanFord
  {a b ℓ n} (rp : RoutingProblem a b ℓ n) where

  open RoutingProblem rp

  I : RMatrix
  I i j with j ≟ᶠ i
  ... | yes _ = 1#
  ... | no  _ = 0#

  -- Algorithm for a single iteration
  σ : RMatrix → RMatrix
  σ X i j = foldr (λ _ → Route) _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

  σ-cong : ∀ {X Y} → X ≈ₘ Y → σ X ≈ₘ σ Y
  σ-cong X≈Y i j = {!foldr-!}

  -- A possible parallelisation of the algorithm
  parallelisation : Parallelisation b ℓ n
  parallelisation = record { 
    Sᵢ = λ _ → DSₜ ; 
    σᵢ = λ i X → σ X i ;
    σᵢ-cong = λ {i} X≈Y → σ-cong X≈Y i }

  -- The asynchronous state function
  δ^ : Schedule n → ℕ → RMatrix → RMatrix
  δ^ = δ^' parallelisation

  -- The synchronous state function
  σ^ : ℕ → RMatrix → RMatrix
  σ^ = σ^' parallelisation
