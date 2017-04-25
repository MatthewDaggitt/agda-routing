open import Algebra.FunctionProperties using (Selective)
open import Data.List.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; sum; map; foldr; concat)
open import Data.List.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _≤?_; z≤n; s≤s; module ≤-Reasoning; ≤-pred)
open import Data.Nat.Properties using (_+-mono_; n∸n≡0; +-∸-assoc; ∸-+-assoc; ≤-step; n≤m+n; m≤m+n; ≰⇒>; 1+n≰n; n≤1+n; m+n∸n≡m)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; +-assoc; +-comm)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset using (⁅_⁆; ⊥; ⊤)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Relation.Binary using (tri<; tri>; tri≈)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; module ≡-Reasoning; inspect; [_]; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Properties using (≈𝔸-refl; ≈𝔸-sym; ≈𝔸-starvationFree; ≈𝔸-appTrans)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∷_∣_; _∺_∣_; source; destination; edge-∷)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty using (SimplePathⁿᵗ; length)
open import RoutingLib.Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; cmp; m∸n≡0⇒m≤n; m≤n⇒m∸n≡0; m<n⇒n∸m≡1+o; <⇒≤; _<?_; <-irrefl)
open import RoutingLib.Routing.Definitions using (RoutingAlgebra; RoutingProblem)
open import RoutingLib.Data.List using (tabulate)

module RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.Activation
  {a b ℓ n-1} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (G : Graph (RoutingAlgebra.Step ra) (suc n-1))
  where

  private

    n : ℕ
    n = suc n-1

  abstract

    open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.Core ra ⊕-sel G
    open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G
    open RoutingAlgebra ra using (refl)

    open Schedule
    open import RoutingLib.Routing.Algorithms.BellmanFord crp using (σ∥; I; δ)
    open RoutingProblem crp using (RMatrix)
    open import RoutingLib.Asynchronous.Snapshot σ∥ using (Snapshot; toListⱼ; _≈ₛ_; snapshot)
    open import RoutingLib.Data.List.Any.GenericMembership (Cₛ) using (_∈_)

    open Parallelisation σ∥ using (_≈ₘ_)

    -----------------------------------------------
    -- Useful operations on activation functions --
    -----------------------------------------------

    -- reset𝔸 prepends a single extra step where every processor activates to the original activation function
    reset𝔸 : 𝔸 n → 𝔸 n
    reset𝔸 α zero          = ⊥
    reset𝔸 α (suc zero)    = ⊤
    reset𝔸 α (suc (suc t)) = α (suc t)

    reset𝔸-≈𝔸 : ∀ α → α ⟦ 0 ⟧≈𝔸⟦ 1 ⟧ reset𝔸 α
    reset𝔸-≈𝔸 α zero          = ≡-refl
    reset𝔸-≈𝔸 α (suc zero)    = ≡-refl
    reset𝔸-≈𝔸 α (suc (suc t)) = cong (λ t → α (2 + t)) (≡-sym (+-suc t 0))

    -- path𝔸 prepends the sequence of activation steps needed to generate the SimplePath provided
    path𝔸 : SimplePathⁿᵗ n → 𝔸 n → 𝔸 n
    path𝔸 _           _ zero          = ⊥
    path𝔸 (i ∺ _ ∣ _) α (suc zero)    = ⁅ i ⁆
    path𝔸 (_ ∺ _ ∣ _) α (suc (suc t)) = α (suc t)
    path𝔸 (i ∷ _ ∣ _) α (suc zero)    = ⁅ i ⁆
    path𝔸 (_ ∷ p ∣ _) α (suc (suc t)) = path𝔸 p α (suc t)
    
    path𝔸-≈𝔸 : ∀ p α → α ⟦ 0 ⟧≈𝔸⟦ length p ⟧ path𝔸 p α
    path𝔸-≈𝔸 (_ ∺ _ ∣ _) α zero          = ≡-refl
    path𝔸-≈𝔸 (_ ∷ p ∣ _) α zero          = path𝔸-≈𝔸 p α zero
    path𝔸-≈𝔸 (_ ∺ _ ∣ _) α (suc zero)    = ≡-refl
    path𝔸-≈𝔸 (_ ∺ _ ∣ _) α (suc (suc t)) = cong (λ t → α (2 + t)) (≡-sym (+-suc t 0))
    path𝔸-≈𝔸 (_ ∷ p ∣ _) α (suc zero)    = path𝔸-≈𝔸 p α (suc zero)
    path𝔸-≈𝔸 (_ ∷ p ∣ _) α (suc (suc t)) rewrite +-suc t (length p) = path𝔸-≈𝔸 p α (suc (suc t))

    -- path&reset𝔸 prepends the sequence of activation steps needed to generate the CRoute provided and then reset the state
    path&reset𝔸 : SimplePathⁿᵗ n → 𝔸 n → 𝔸 n
    path&reset𝔸 p α = reset𝔸 (path𝔸 p α)

    path&reset𝔸-≈𝔸 : ∀ p α → α ⟦ zero ⟧≈𝔸⟦ 1 + length p ⟧ path&reset𝔸 p α 
    path&reset𝔸-≈𝔸 p = ≈𝔸-appTrans reset𝔸 (path𝔸 p) reset𝔸-≈𝔸 (path𝔸-≈𝔸 p)



    ---------------------------------------------
    -- Activation functions for building state --
    ---------------------------------------------

    -- allStates𝔸 prepends to α the sequence of activation steps needed to generate each CRoute in turn 
    allStates𝔸 : ∀ {xs} → All NonTrivialState xs → 𝔸 n → 𝔸 n
    allStates𝔸 []                             α = α
    allStates𝔸 ((ntState {p = p} _ _ _) ∷ xs) α = path&reset𝔸 p (allStates𝔸 xs α)

    state𝔸 : RMatrix → 𝔸 n → 𝔸 n
    state𝔸 X = allStates𝔸 (all-nonTrivialStates X)

{-
    allStates𝔸-≈𝔸 : ∀ {xs} (pxs : All NonTrivialState xs) α → α ⟦ 0 ⟧≈𝔸⟦ map suc xs ⟧ all𝔸 pxs α 
    allStates𝔸-≈𝔸 []                        α t = ≡-refl
    allStates𝔸-≈𝔸 (croute _ [ p ] _ _ ∷ xs)     = ≈𝔸-appTrans (path&reset𝔸 p) (all𝔸 xs) (path&reset𝔸-≈𝔸 p) (all𝔸-≈𝔸 xs)
-}

    ------------------------------------------------
    -- Activation functions for building messages --
    ------------------------------------------------

    allMessages𝔸 : ∀ {xs} → All NonTrivialMessage xs → 𝔸 n → 𝔸 n
    allMessages𝔸 []                             α = α
    allMessages𝔸 ((ntMessage {p = p} _ _) ∷ xs) α = path&reset𝔸 p (allMessages𝔸 xs α)

    messages𝔸 : ∀ {β tₛ} → Dynamic β → Snapshot β tₛ → 𝔸 n → 𝔸 n
    messages𝔸 dyn sn = allMessages𝔸 (all-nonTrivialMessages dyn sn)


    --------------------------------
    -- Final activation functions --
    --------------------------------

    -- The completed activation function
    final𝔸 : ∀ (𝕤 : Schedule n) tₛ → RMatrix → Snapshot (β 𝕤) tₛ → 𝔸 n
    final𝔸 𝕤 tₛ X sn t with cmp t (build𝕋 X (dynamic 𝕤) sn)
    ... | tri> _ _ _ = α 𝕤 (t ∸ build𝕋 X (dynamic 𝕤) sn + tₛ)
    ... | tri≈ _ _ _ = ⊤
    ... | tri< _ _ _ = state𝔸 X (messages𝔸 (dynamic 𝕤) sn (α 𝕤)) t

    final𝔸-≈𝔸 : ∀ 𝕤 tₛ X (sn : Snapshot (β 𝕤) tₛ) → α 𝕤 ⟦ tₛ ⟧≈𝔸⟦ build𝕋 X (dynamic 𝕤) sn ⟧ final𝔸 𝕤 tₛ X sn  
    final𝔸-≈𝔸 𝕤 tₛ X sn t with cmp (suc t + build𝕋 X (dynamic 𝕤) sn) (build𝕋 X (dynamic 𝕤) sn)
    ... | tri> _ _ _          = cong (λ t → α 𝕤 (t + tₛ)) (≡-sym (m+n∸n≡m (suc t) (build𝕋 X (dynamic 𝕤) sn)))
    ... | tri≈ _ _ b𝕋≮1+t+b𝕋 = contradiction (s≤s (n≤m+n t (build𝕋 X (dynamic 𝕤) sn))) b𝕋≮1+t+b𝕋
    ... | tri< _ _ b𝕋≮1+t+b𝕋 = contradiction (s≤s (n≤m+n t (build𝕋 X (dynamic 𝕤) sn))) b𝕋≮1+t+b𝕋

    final𝔸-starvationFree : ∀ 𝕤 tₛ X (sn : Snapshot (β 𝕤) tₛ) → StarvationFree (final𝔸 𝕤 tₛ X sn)
    final𝔸-starvationFree 𝕤 tₛ X sn = ≈𝔸-starvationFree (starvationFree 𝕤) (final𝔸-≈𝔸 𝕤 tₛ X sn)
