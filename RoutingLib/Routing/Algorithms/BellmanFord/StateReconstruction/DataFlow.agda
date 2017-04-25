open import Algebra.FunctionProperties using (Selective)
open import Data.List.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; sum; map; foldr; concat)
open import Data.List.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _≤?_; z≤n; s≤s; module ≤-Reasoning; ≤-pred)
open import Data.Nat.Properties using (_+-mono_; n∸n≡0; +-∸-assoc; ∸-+-assoc; ≤-step; n≤m+n; m≤m+n; ≰⇒>; m+n∸n≡m; m+n∸m≡n; ∸-mono)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; +-assoc; +-comm)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (∃; ∃₂; _,_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; subst; module ≡-Reasoning) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Properties using (≈𝔹-appTrans)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∷_∣_; _∺_∣_; source; destination; edge-∷)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty using (SimplePathⁿᵗ; length)
open import RoutingLib.Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; _<?_; <-irrefl; cmp; m∸n≡0⇒m≤n; m∸n+n≡m; m≤n⇒m∸n≡0; m+o≡n⇒m≡n∸o; m<n⇒n∸m≡1+o; <⇒≤; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≢; +-monoᵣ-<; m+n≮n; suc-injective; ≤-stepsᵣ; m+o≤n⇒m≤n∸o)
open import RoutingLib.Routing.Definitions using (RoutingAlgebra; RoutingProblem)
open import RoutingLib.Data.List using (tabulate)

module RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.DataFlow
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

    ----------------------------------------------
    -- Useful operations on data flow functions --
    ----------------------------------------------

    -- reset𝔹 prepends a given data flow function such that at time 1 every node accesses the original state at time 0
    reset𝔹 : 𝔹 n → 𝔹 n
    reset𝔹 β zero          i j = zero
    reset𝔹 β (suc zero)    i j = zero
    reset𝔹 β (suc (suc t)) i j = suc (β (suc t) i j)
    
    reset𝔹-≈𝔹 : ∀ β → β ⟦ 0 ⟧≈𝔹⟦ 1 ⟧ reset𝔹 β
    reset𝔹-≈𝔹 β zero i j                      = ≡-refl
    reset𝔹-≈𝔹 β (suc t) i j rewrite +-suc t 0 = ≡-refl

    reset𝔹-causal : ∀ {β} → Causal β → Causal (reset𝔹 β)
    reset𝔹-causal causal zero i j    = s≤s z≤n
    reset𝔹-causal causal (suc t) i j = s≤s (causal t i j)

    reset𝔹-dynamic : ∀ {β} → Dynamic β → Dynamic (reset𝔹 β)
    reset𝔹-dynamic {β} dyn zero    i j = 1 , λ {(s≤s (s≤s z≤n)) ()}
    reset𝔹-dynamic {β} dyn (suc t) i j with dyn t i j
    ... | tᶠ , tᶠ-final = suc tᶠ , 1+tᶠ-final
      where
      1+tᶠ-final : ∀ {t'} → suc (suc tᶠ) ≤ t' → reset𝔹 β t' i j ≢ suc t
      1+tᶠ-final {zero}         ()
      1+tᶠ-final {suc zero}     (s≤s ())
      1+tᶠ-final {suc (suc t')} (s≤s 1+tᶠ≤1+t') = (tᶠ-final 1+tᶠ≤1+t') ∘ suc-injective


    -- revPath𝔹 generates a data flow function that will generate the required SimplePath in reverse
    revPath𝔹 : SimplePathⁿᵗ n → 𝔹 n
    revPath𝔹 (_ ∺ _ ∣ _) _       _ _ = zero
    revPath𝔹 (_ ∷ p ∣ _) (suc t) i j = revPath𝔹 p t i j
    revPath𝔹 (k ∷ p ∣ _) zero    i j with i ≟ k | j ≟ source p
    ... | no  _ | _     = zero
    ... | _     | no  _ = zero
    ... | yes _ | yes _ = length p

    postulate test : ∀ m n {o} → n ∸ m ≡ suc o → o ≡ n ∸ suc m
    
    revPath𝔹-causal : ∀ p t i j → revPath𝔹 p (length p ∸ t) i j ≤ t
    revPath𝔹-causal (_ ∺ _ ∣ _) _ _ _ = z≤n
    revPath𝔹-causal (_ ∷ p ∣ _) zero i j = revPath𝔹-causal p zero i j
    revPath𝔹-causal (k ∷ p ∣ _) (suc t) i j with length p ≤? t
    revPath𝔹-causal (k ∷ p ∣ _) (suc t) i j | yes |p|≤t rewrite m≤n⇒m∸n≡0 |p|≤t with i ≟ k | j ≟ source p
    ... | no  _ | _     = z≤n
    ... | yes _ | no  _ = z≤n
    ... | yes _ | yes _ = ≤-step |p|≤t
    revPath𝔹-causal (k ∷ p ∣ _) (suc t) i j | no  |p|≰t with m<n⇒n∸m≡1+o (≰⇒> |p|≰t)
    ...   | o , |p|∸t≡1+o rewrite |p|∸t≡1+o | test t (length p) |p|∸t≡1+o = revPath𝔹-causal p (suc t) i j

    revPath𝔹-dynamic : ∀ p t i j → revPath𝔹 p t i j < length p
    revPath𝔹-dynamic (_ ∺ _ ∣ _) _       _ _ = s≤s z≤n
    revPath𝔹-dynamic (_ ∷ p ∣ _) (suc t) i j = ≤-step (revPath𝔹-dynamic p t i j)
    revPath𝔹-dynamic (k ∷ p ∣ _) zero    i j with i ≟ k | j ≟ source p
    ... | no  _ | _     = s≤s z≤n
    ... | yes _ | no  _ = s≤s z≤n
    ... | yes _ | yes _ = ≤-refl


    -- path𝔹 prepends the provided data flow function with the sequence of steps necessary to generate the provided path
    path𝔹 : SimplePathⁿᵗ n → 𝔹 n → 𝔹 n
    path𝔹 p β t i j with t ≤? length p
    ... | yes _ = revPath𝔹 p (suc (length p) ∸ t) i j
    ... | no  _ = length p + β (t ∸ length p) i j

    path𝔹-≈𝔹 : ∀ p β → β ⟦ 0 ⟧≈𝔹⟦ length p ⟧ path𝔹 p β
    path𝔹-≈𝔹 p β t i j with suc (t + length p) ≤? length p
    ... | yes t+|p|<|p| = contradiction t+|p|<|p| (m+n≮n t (length p))
    ... | no  t+|p|≮|p| = ≡-sym (
      begin
        length p + β (suc t + length p ∸ length p) i j ∸ length p  ≡⟨ cong (λ t → length p + β t i j ∸ length p) (m+n∸n≡m (suc t) (length p)) ⟩
        length p + β (suc t) i j ∸ length p                        ≡⟨ cong (_∸ length p) (+-comm (length p) _) ⟩
        β (suc t) i j + length p ∸ length p                        ≡⟨ m+n∸n≡m (β (suc t) i j) (length p) ⟩
        β (suc t) i j                                              ≡⟨ cong (λ t → β t i j) (≡-sym (+-right-identity (suc t))) ⟩
        β (suc t + 0) i j
      ∎)
      where open ≡-Reasoning

    path𝔹-causal : ∀ {β} → Causal β → ∀ p → Causal (path𝔹 p β)
    path𝔹-causal {β} causal p t i j with suc t ≤? length p
    ... | yes _     = s≤s (revPath𝔹-causal p t i j)
    ... | no  t≮|p| = 
      begin
        suc (length p) + β (suc t ∸ length p)   i j ≡⟨ cong (suc (length p) +_) (cong (λ t → β t i j) (+-∸-assoc 1 (≮⇒≥ t≮|p|))) ⟩
        suc (length p) + β (suc (t ∸ length p)) i j ≤⟨ +-monoᵣ-< (≤-refl {length p}) (causal (t ∸ length p) i j) ⟩
        length p + (suc (t ∸ length p))             ≡⟨ cong (length p +_) (≡-sym (+-∸-assoc 1 (≮⇒≥ t≮|p|))) ⟩
        length p + (suc t ∸ length p)               ≡⟨ m+n∸m≡n (≰⇒≥ t≮|p|) ⟩
        suc t
      ∎
      where open ≤-Reasoning

    path𝔹-dynamic : ∀ {β} → Dynamic β → ∀ p → Dynamic (path𝔹 p β)
    path𝔹-dynamic {β} dyn p t i j with suc t ≤? length p
    ... | yes t<|p| = length p , |p|-final
      where
      |p|-final : ∀ {t'} → length p < t' → path𝔹 p β t' i j ≢ t
      |p|-final {t'} |p|<t' with t' ≤? length p
      ... | yes t'≤|p| = contradiction t'≤|p| (<⇒≱ |p|<t')
      ... | no  _      = (<⇒≢ (≤-stepsᵣ (β (t' ∸ length p) i j) t<|p|)) ∘ ≡-sym
    ... | no  t≮|p| with dyn (t ∸ length p) i j
    ...   | tᶠ , tᶠ-final = length p + tᶠ , |p|+tᶠ-final
      where
      |p|+tᶠ-final : ∀ {t'} → length p + tᶠ < t' → path𝔹 p β t' i j ≢ t
      |p|+tᶠ-final {t'} |p|+tᶠ<t' |p|+β≡t with t' ≤? length p
      ... | yes _ = <⇒≢ (≤-trans (revPath𝔹-dynamic p (suc (length p) ∸ t') i j) (≮⇒≥ t≮|p|)) |p|+β≡t
      ... | no  _ = tᶠ-final (m+o≤n⇒m≤n∸o (≤-trans (≤-reflexive (cong suc (+-comm tᶠ (length p)))) |p|+tᶠ<t')) (m+o≡n⇒m≡n∸o (≡-trans (+-comm _ (length p)) |p|+β≡t))


    -- path&reset𝔹 prepends β with the sequence of flows needed to generate the CRoute provided and then reset the state
    path&reset𝔹 : SimplePathⁿᵗ n → 𝔹 n → 𝔹 n
    path&reset𝔹 p β = reset𝔹 (path𝔹 p β)

    path&reset𝔹-≈𝔹 : ∀ p β → β ⟦ 0 ⟧≈𝔹⟦ 1 + length p ⟧ path&reset𝔹 p β 
    path&reset𝔹-≈𝔹 p β = ≈𝔹-appTrans reset𝔹 (path𝔹 p) 1 (length p) reset𝔹-≈𝔹 (path𝔹-≈𝔹 p) β

    path&reset𝔹-causal : ∀ p {β} → Causal β → Causal (path&reset𝔹 p β)
    path&reset𝔹-causal p causal t i j = reset𝔹-causal (path𝔹-causal causal p) t i j



    --------------------------------------------
    -- Data flow functions for building state --
    --------------------------------------------

    -- allStates𝔹 prepends to α the sequence of activation steps needed to generate each CRoute in turn 
    allStates𝔹 : ∀ {xs} → All NonTrivialState xs → 𝔹 n → 𝔹 n
    allStates𝔹 []                             α = α
    allStates𝔹 ((ntState {p = p} _ _ _) ∷ xs) α = path&reset𝔹 p (allStates𝔹 xs α)

    state𝔹 : RMatrix → 𝔹 n → 𝔹 n
    state𝔹 X = allStates𝔹 (all-nonTrivialStates X)


    postulate state𝔹-causal : ∀ X {β} → Causal β → Causal (state𝔹 X β)
{-

    -- all𝔹 prepends β with the sequence of flows needed to generate each CRoute in turn 
    all𝔹 : List CRoute → 𝔹 n → 𝔹 n
    all𝔹 []                        β = β
    all𝔹 (cnull              ∷ xs) β = all𝔹 xs β
    all𝔹 (croute _ []    _ _ ∷ xs) β = all𝔹 xs β
    all𝔹 (croute _ [ p ] _ _ ∷ xs) β = path&reset𝔹 p (all𝔹 xs β)

    all𝔹-≈𝔹 : ∀ xs β → β ⟦ 0 ⟧≈𝔹⟦ lc𝕋 xs ⟧ all𝔹 xs β 
    all𝔹-≈𝔹 []                        β t i j = ≡-refl
    all𝔹-≈𝔹 (cnull              ∷ xs)         = all𝔹-≈𝔹 xs
    all𝔹-≈𝔹 (croute _ []    _ _ ∷ xs)         = all𝔹-≈𝔹 xs
    all𝔹-≈𝔹 (croute _ [ p ] _ _ ∷ xs)         = ≈𝔹-appTrans (path&reset𝔹 p) (all𝔹 xs) (1 + length p) (lc𝕋 xs) (path&reset𝔹-≈𝔹 p) (all𝔹-≈𝔹 xs)

    all𝔹-causal : ∀ xs {β} → Causal β → Causal (all𝔹 xs β)
    all𝔹-causal []                        {β} causal = causal
    all𝔹-causal (cnull              ∷ xs) {β} causal = all𝔹-causal xs causal
    all𝔹-causal (croute _ []    _ _ ∷ xs) {β} causal = all𝔹-causal xs causal
    all𝔹-causal (croute _ [ p ] _ _ ∷ xs) {β} causal = path&reset𝔹-causal p (all𝔹-causal xs causal)

    all𝔹-dynamic : ∀ xs {β} → Dynamic β → Dynamic (all𝔹 xs β)
    all𝔹-dynamic []                        dyn = dyn
    all𝔹-dynamic (cnull              ∷ xs) dyn = all𝔹-dynamic xs dyn
    all𝔹-dynamic (croute _ []    _ _ ∷ xs) dyn = all𝔹-dynamic xs dyn
    all𝔹-dynamic (croute _ [ p ] _ _ ∷ xs) dyn = {!!} --path&reset𝔹-dynamic p (all𝔹-dynamic xs dynamic)
-}


    -----------------------------------------------
    -- Data flow functions for building messages --
    -----------------------------------------------

    allMessages𝔹 : ∀ {xs} → All NonTrivialMessage xs → 𝔹 n → 𝔹 n
    allMessages𝔹 []                             α = α
    allMessages𝔹 ((ntMessage {p = p} _ _) ∷ xs) α = path&reset𝔹 p (allMessages𝔹 xs α)

    messages𝔹 : ∀ {β tₛ} → Dynamic β → Snapshot β tₛ → 𝔹 n → 𝔹 n
    messages𝔹 dyn sn = allMessages𝔹 (all-nonTrivialMessages dyn sn)

    postulate messages𝔹-causal : ∀ {β tₛ} dyn (sn : Snapshot β tₛ) → ∀ {β₂} → Causal β₂ → Causal (messages𝔹 dyn sn β₂)
    
    ------------------------------
    -- Final data flow function --
    ------------------------------

    -- final𝔹 prepends β with the sequence of flows needed to generate the provided state and messages in flight
    final𝔹 : ∀ (𝕤 : Schedule n) tₛ → RMatrix → Snapshot (β 𝕤) tₛ → 𝔹 n
    final𝔹 𝕤 tₛ X sn t i j with cmp t (build𝕋𝔸 X (dynamic 𝕤) sn) | β 𝕤 (t ∸ build𝕋𝔸 X (dynamic 𝕤) sn + tₛ) i j ≤? tₛ
    ... | tri< _ _ _ | _        = state𝔹 X (messages𝔹 (dynamic 𝕤) sn (β 𝕤)) t i j
    ... | tri≈ _ _ _ | _        = indexState X i j
    ... | tri> _ _ _ | no  _    = β 𝕤 (t ∸ build𝕋𝔸 X (dynamic 𝕤) sn + tₛ) i j  ∸ tₛ + build𝕋𝔸 X (dynamic 𝕤) sn
    ... | tri> _ _ _ | yes β≤tₛ = indexMessage X (dynamic 𝕤) sn i j (t ∸ build𝕋𝔸 X (dynamic 𝕤) sn + tₛ) (n≤m+n (t ∸ build𝕋𝔸 X (dynamic 𝕤) sn) tₛ) β≤tₛ

    final𝔹-≈𝔹 : ∀ 𝕤 tₛ X (sn : Snapshot (β 𝕤) tₛ) → β 𝕤 ⟦ tₛ ⟧≈𝔹⟦ build𝕋𝔸 X (dynamic 𝕤) sn ⟧ final𝔹 𝕤 tₛ X sn  
    final𝔹-≈𝔹 𝕤 tₛ X sn t i j with cmp (suc t + build𝕋𝔸 X (dynamic 𝕤) sn) (build𝕋𝔸 X (dynamic 𝕤) sn) | β 𝕤 (suc t + build𝕋𝔸 X (dynamic 𝕤) sn ∸ build𝕋𝔸 X (dynamic 𝕤) sn + tₛ) i j ≤? tₛ
    ... | tri< _ _ b𝕋≮1+t+b𝕋 | _        = contradiction (s≤s (n≤m+n t (build𝕋𝔸 X (dynamic 𝕤) sn))) b𝕋≮1+t+b𝕋
    ... | tri≈ _ _ b𝕋≮1+t+b𝕋 | _        = contradiction (s≤s (n≤m+n t (build𝕋𝔸 X (dynamic 𝕤) sn))) b𝕋≮1+t+b𝕋
    ... | tri> _ _ _          | no  _    = ≡-sym (≡-trans (m+n∸n≡m _ (build𝕋𝔸 X (dynamic 𝕤) sn)) (cong (λ t → β 𝕤 (t + tₛ) i j ∸ tₛ) (m+n∸n≡m (suc t) (build𝕋𝔸 X (dynamic 𝕤) sn))))
    ... | tri> _ _ _          | yes β≤tₛ = ≡-trans 
                                            (m≤n⇒m∸n≡0 (subst (λ t → β 𝕤 (t + tₛ) i j ≤ tₛ) (m+n∸n≡m (suc t) (build𝕋𝔸 X (dynamic 𝕤) sn)) β≤tₛ)) 
                                            (≡-sym (m≤n⇒m∸n≡0 (≤-trans (<⇒≤ (indexMessage<build𝕋 X (dynamic 𝕤) sn i j _ _ β≤tₛ)) (≤-reflexive (cong (λ f → f X (dynamic 𝕤) sn) build𝕋𝔸-≡))))) -- REPLACE when 𝔸 gone

    final𝔹-causal : ∀ 𝕤 tₛ X (sn : Snapshot (β 𝕤) tₛ) → Causal (final𝔹 𝕤 tₛ X sn)
    final𝔹-causal 𝕤 tₛ X sn t i j with cmp (suc t) (build𝕋𝔸 X (dynamic 𝕤) sn) | β 𝕤 (suc t ∸ build𝕋𝔸 X (dynamic 𝕤) sn + tₛ) i j ≤? tₛ
    ... | tri< 1+t<b𝕋 _ _ | _        = state𝔹-causal X (messages𝔹-causal (dynamic 𝕤) sn (causal 𝕤)) t i j
    ... | tri≈ _ 1+t≡b𝕋 _ | _        = ≤-trans (indexState<build𝕋 X (dynamic 𝕤) sn i j) (≤-reflexive (≡-trans (cong (λ f → f X (dynamic 𝕤) sn) build𝕋𝔸-≡) (≡-sym 1+t≡b𝕋)))  -- REPLACE when 𝔸 gone
    ... | tri> _ _ b𝕋<1+t | yes β≤tₛ = ≤-trans (indexMessage<build𝕋 X (dynamic 𝕤) sn i j _ _ _) (≤-trans (≤-step (≤-reflexive (cong (λ f → f X (dynamic 𝕤) sn) build𝕋𝔸-≡))) b𝕋<1+t) -- REPLACE when 𝔸 gone
    ... | tri> _ _ b𝕋<1+t | no β≰tₛ   = 
      begin
        suc (β 𝕤 (suc t ∸ b𝕋 + tₛ) i j ∸ tₛ) + b𝕋    ≡⟨ cong (_+ b𝕋) (≡-sym (+-∸-assoc 1 (≰⇒≥ β≰tₛ))) ⟩
        suc (β 𝕤 (suc t ∸ b𝕋 + tₛ) i j) ∸ tₛ + b𝕋    ≡⟨ cong (λ t → suc (β 𝕤 (t + tₛ) i j) ∸ tₛ + b𝕋) (+-∸-assoc 1 (≤-pred b𝕋<1+t)) ⟩
        suc (β 𝕤 (suc (t ∸ b𝕋 + tₛ)) i j) ∸ tₛ + b𝕋  ≤⟨ _+-mono_ (∸-mono (causal 𝕤 (t ∸ b𝕋 + tₛ) i j) (≤-refl {tₛ})) (≤-refl {b𝕋}) ⟩
        suc (t ∸ b𝕋) + tₛ ∸ tₛ + b𝕋                  ≡⟨ cong (_+ b𝕋) (m+n∸n≡m (suc (t ∸ b𝕋)) tₛ) ⟩
        suc (t ∸ b𝕋) + b𝕋                           ≡⟨ cong (_+ b𝕋) (≡-sym (+-∸-assoc 1 (≤-pred b𝕋<1+t))) ⟩
        suc t ∸ b𝕋 + b𝕋                             ≡⟨ m∸n+n≡m (<⇒≤ b𝕋<1+t) ⟩
        suc t
      ∎
      where 
      b𝕋 = build𝕋𝔸 X (dynamic 𝕤) sn
      open ≤-Reasoning

    postulate final𝔹-dynamic : ∀ 𝕤 tₛ X (sn : Snapshot (β 𝕤) tₛ) → Dynamic (final𝔹 𝕤 tₛ X sn)
    --final𝔹
