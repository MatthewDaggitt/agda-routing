open import Algebra.FunctionProperties using (Selective)
open import Data.List.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; sum; map; foldr; concat)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _≤?_; z≤n; s≤s; module ≤-Reasoning; ≤-pred)
open import Data.Nat.Properties using (_+-mono_; n∸n≡0; +-∸-assoc; ∸-+-assoc; ≤-step; n≤m+n; m≤m+n; ≰⇒>)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; +-assoc; +-comm)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset using (⁅_⁆; ⊤)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Relation.Binary using (tri<; tri>; tri≈)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; module ≡-Reasoning; inspect; [_]; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Properties using (≈𝔸-refl; ≈𝔸-sym; ≈𝔸-starvationFree; ≈𝔹-dynamic; ≈𝔹-sym)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∷_∣_; _∺_∣_; source; destination; edge-∷)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty using (SimplePathⁿᵗ; length)
open import RoutingLib.Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; cmp; m∸n≡0⇒m≤n; m≤n⇒m∸n≡0; m<n⇒n∸m≡1+o; <⇒≤)
open import RoutingLib.Routing.Definitions using (RoutingAlgebra; RoutingProblem)
open import RoutingLib.Data.List using (tabulate)

module RoutingLib.Routing.Algorithms.BellmanFord.AddingPaths.SnapshotReconstruction
  {a b ℓ n-1} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (G : Graph (RoutingAlgebra.Step ra) (suc n-1))
  where

  private

    n : ℕ
    n = suc n-1

  abstract

    open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G
    open RoutingAlgebra ra using (refl)

    open Schedule
    open import RoutingLib.Routing.Algorithms.BellmanFord crp using (σ∥; I; δ)
    open RoutingProblem crp using (RMatrix)
    open import RoutingLib.Asynchronous.Snapshot σ∥ using (Snapshot; toListⱼ; _≈ₛ_; snapshot)
    open import RoutingLib.Data.List.Any.GenericMembership (Cₛ) using (_∈_)

    open Parallelisation σ∥ using (_≈ₘ_)

    stateToList : RMatrix → List CRoute
    stateToList X = concat (map tabulate (tabulate X))

    messagesToList : ∀ {β t} → Dynamic β → Snapshot β t → List CRoute
    messagesToList dyn sn = {!!}



    -----------------------------------
    -- Time taken for reconstruction --
    -----------------------------------

    -- The amount of time required to construct a schedule resulting in a given list of croutes
    listConstruction𝕋 : List CRoute → 𝕋
    listConstruction𝕋 []                        = zero
    listConstruction𝕋 (cnull              ∷ xs) = listConstruction𝕋 xs
    listConstruction𝕋 (croute _ []    _ _ ∷ xs) = listConstruction𝕋 xs
    listConstruction𝕋 (croute _ [ p ] _ _ ∷ xs) = suc (length p) + listConstruction𝕋 xs

    -- The amount of time required to construct a schedule resulting in a matrix and a given set of messages
    construction𝕋 : RMatrix → ∀ {β t} → Dynamic β → Snapshot β t → 𝕋
    construction𝕋 X dyn sn = listConstruction𝕋 (messagesToList dyn sn ++ stateToList X)



    -------------------------------------
    -- Reconstruct activation function --
    -------------------------------------

    -- reset𝔸 prepends a single extra step where every processor activates to the original activation function
    reset𝔸 : 𝔸 n → 𝔸 n
    reset𝔸 α zero    = ⊤
    reset𝔸 α (suc t) = α t

    -- path𝔸 prepends the sequence of activation steps needed to generate the SimplePath provided
    path𝔸 : SimplePathⁿᵗ n → 𝔸 n → 𝔸 n
    path𝔸 (i ∺ _ ∣ _) α zero    = ⁅ i ⁆
    path𝔸 (_ ∺ _ ∣ _) α (suc t) = α t
    path𝔸 (i ∷ _ ∣ _) α zero    = ⁅ i ⁆
    path𝔸 (_ ∷ p ∣ _) α (suc t) = path𝔸 p α t

    -- route&reset prepends the sequence of activation steps needed to generate the CRoute provided and then reset the state
    path&reset𝔸 : SimplePathⁿᵗ n → 𝔸 n → 𝔸 n
    path&reset𝔸 p α = reset𝔸 (path𝔸 p α)

    -- all𝔸 prepends to α the sequence of activation steps needed to generate each CRoute in turn 
    all𝔸 : List CRoute → 𝔸 n → 𝔸 n
    all𝔸 []                        α = α
    all𝔸 (cnull              ∷ xs) α = all𝔸 xs α
    all𝔸 (croute _ []    _ _ ∷ xs) α = all𝔸 xs α
    all𝔸 (croute _ [ p ] _ _ ∷ xs) α = path&reset𝔸 p (all𝔸 xs α)

    -- construction𝔸 prepends the activation sequence required to generate the provided state and messages in flight
    construction𝔸 : ∀ (𝕤 : Schedule n) t → RMatrix → Snapshot (Schedule.β 𝕤) t → 𝔸 n
    construction𝔸 𝕤 t X sn = all𝔸 (messagesToList (dynamic 𝕤) sn ++ stateToList X) α


    -- Properties

    reset𝔸-≈𝔸 : ∀ α → α ⟦ 0 ⟧≈𝔸⟦ 1 ⟧ reset𝔸 α
    reset𝔸-≈𝔸 α zero    = ≡-refl
    reset𝔸-≈𝔸 α (suc t) = cong α (≡-sym (+-suc t 0))

    path𝔸-≈𝔸 : ∀ p α → α ⟦ 0 ⟧≈𝔸⟦ length p ⟧ path𝔸 p α
    path𝔸-≈𝔸 (_ ∺ _ ∣ _) α zero    = ≡-refl
    path𝔸-≈𝔸 (_ ∺ _ ∣ _) α (suc t) = cong α (≡-sym (+-suc t 0))
    path𝔸-≈𝔸 (_ ∷ p ∣ _) α zero    = path𝔸-≈𝔸 p α zero
    path𝔸-≈𝔸 (i ∷ p ∣ _) α (suc t) rewrite +-suc t (length p) = path𝔸-≈𝔸 p α (suc t)

    path&reset𝔸-≈𝔸 : ∀ p α → α ⟦ zero ⟧≈𝔸⟦ suc (length p) ⟧ path&reset𝔸 p α 
    path&reset𝔸-≈𝔸 p α t = 
      begin
        α (t + 0)                                ≡⟨ path𝔸-≈𝔸 p α t ⟩
        path𝔸 p α (t + length p)                ≡⟨ cong (path𝔸 p α) (≡-sym (+-right-identity _)) ⟩
        path𝔸 p α (t + length p + 0)            ≡⟨ reset𝔸-≈𝔸 (path𝔸 p α) (t + length p)  ⟩
        reset𝔸 (path𝔸 p α) (t + length p + 1)   ≡⟨ cong (reset𝔸 (path𝔸 p α)) (+-assoc t _ _) ⟩
        reset𝔸 (path𝔸 p α) (t + (length p + 1)) ≡⟨ cong (λ v → reset𝔸 (path𝔸 p α) (t + v)) (+-comm _ 1) ⟩
        reset𝔸 (path𝔸 p α) (t + suc (length p))
      ∎
      where open ≡-Reasoning

    all𝔸-≈𝔸 : ∀ xs α → α ⟦ 0 ⟧≈𝔸⟦ listConstruction𝕋 xs ⟧ all𝔸 xs α 
    all𝔸-≈𝔸 []                        α t = ≡-refl
    all𝔸-≈𝔸 (cnull              ∷ xs) α t = all𝔸-≈𝔸 xs α t 
    all𝔸-≈𝔸 (croute _ []    _ _ ∷ xs) α t = all𝔸-≈𝔸 xs α t
    all𝔸-≈𝔸 (croute _ [ p ] _ _ ∷ xs) α t = 
      begin
        α (t + 0)                                                              ≡⟨ all𝔸-≈𝔸 xs α t ⟩
        all𝔸 xs α (t + listConstruction𝕋 xs)                                    ≡⟨ cong (all𝔸 xs α) (≡-sym (+-right-identity _)) ⟩
        all𝔸 xs α (t + listConstruction𝕋 xs + 0)                                ≡⟨ path&reset𝔸-≈𝔸 p (all𝔸 xs α) (t + listConstruction𝕋 xs) ⟩
        path&reset𝔸 p (all𝔸 xs α) (t + listConstruction𝕋 xs + suc (length p))   ≡⟨ cong (path&reset𝔸 p (all𝔸 xs α)) (+-assoc t _ _) ⟩
        path&reset𝔸 p (all𝔸 xs α) (t + (listConstruction𝕋 xs + suc (length p))) ≡⟨ cong (λ v → path&reset𝔸 p (all𝔸 xs α) (t + v)) (+-comm _ (suc (length p))) ⟩
        path&reset𝔸 p (all𝔸 xs α) (t + (suc (length p) + listConstruction𝕋 xs))
      ∎
      where open ≡-Reasoning

{-
    all𝔸-starvationFree : ∀ {α} xs → StarvationFree α → StarvationFree (all𝔸 xs α)
    all𝔸-starvationFree {α} xs sf = ≈𝔸-starvationFree sf (all𝔸-≈𝔸 xs α)
-}


    ------------------------------------
    -- Reconstruct data flow function --
    ------------------------------------

    -- reset𝔹 prepends a given data flow function such that every flow activates
    reset𝔹 : 𝔹 n → 𝔹 n
    reset𝔹 β zero          i j = zero
    reset𝔹 β (suc zero)    i j = zero
    reset𝔹 β (suc (suc t)) i j = β (suc t) i j

    reset𝔹-causal : ∀ {β} → Causal β → Causal (reset𝔹 β)
    reset𝔹-causal causal zero i j    = s≤s z≤n
    reset𝔹-causal causal (suc t) i j = s≤s (<⇒≤ (causal t i j))

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

{-

    revPath𝔹-causal2 : ∀ p t i j → revPath𝔹 p (length p ∸ suc t) i j ≤ t
    revPath𝔹-causal2 [] _ _ _ = z≤n
    revPath𝔹-causal2 [ _ ∺ _ ∣ _ ] _ _ _ = z≤n
    revPath𝔹-causal2 [ i ∷ i₁ ∺ j ∣ x ∣ x₁ ] zero i₂ j₁ = z≤n
    revPath𝔹-causal2 [ i ∷ i₁ ∷ p ∣ x ∣ x₁ ] zero i₂ j = revPath𝔹-causal2 [ i₁ ∷ p ∣ x ] zero i₂ j
    revPath𝔹-causal2 [ k ∷ p ∣ _ ] (suc t) i j = {!!}
-}



{-
    -- path𝔹 prepends the provided data flow function with the sequence of steps necessary to generate the provided path
    path𝔹 : SimplePathⁿᵗ n → 𝔹 n → 𝔹 n
    path𝔹 p β zero    i j = zero
    path𝔹 p β (suc t) i j with (suc t) ≤? (length p)
    ... | yes _ = revPath𝔹 p (length p ∸ suc t) i j
    ... | no  _ = length p + β (suc t ∸ length p) i j
    
    path𝔹-causal : ∀ p {β} → Causal β → Causal (path𝔹 p β)
    path𝔹-causal p causal t i j with suc t ≤? length p
    ... | yes _       = s≤s {!!} --s≤s (revPath𝔹-causal p t i j)
    ... | no  1+t≰|p| = s≤s {!!}


    


    -- route

    path&reset𝔹 : SimplePathⁿᵗ n → 𝔹 n → 𝔹 n
    path&reset𝔹 p β = reset𝔹 (path𝔹 p β)

    path&reset𝔹-causal : ∀ p {β} → Causal β → Causal (path&reset𝔹 p β)
    path&reset𝔹-causal = {!!}

    path&reset𝔹-dynamic : ∀ p {β} → Dynamic β → Dynamic (path&reset𝔹 p β)
    path&reset𝔹-dynamic = {!!}


    -- all𝔹

    all𝔹 : List CRoute → 𝔹 n
    all𝔹 []                        t i j = zero
    all𝔹 (cnull              ∷ xs) t i j = all𝔹 xs t i j
    all𝔹 (croute _ []    _ _ ∷ xs) t i j = all𝔹 xs t i j
    all𝔹 (croute _ [ p ] _ _ ∷ xs) t i j = path&reset𝔹 p (all𝔹 xs) t i j

{-
    all𝔹-≈𝔹 : ∀ xs β → all𝔹 xs β ⟦ listConstruction𝕋 xs ⟧≈𝔹⟦ zero ⟧ β
    all𝔹-≈𝔹 []                  β t i j = ≡-refl
    all𝔹-≈𝔹 (cnull        ∷ xs) β t i j = all𝔹-≈𝔹 xs β t i j
    all𝔹-≈𝔹 (croute _ p _ ∷ xs) β t i j = 
      begin
        route𝔹 p (all𝔹 xs β) (suc t + (length p + listConstruction𝕋 xs)) i j ∸ (length p + listConstruction𝕋 xs)  ≡⟨ ≡-sym (∸-+-assoc _ (length p) _) ⟩
        (route𝔹 p (all𝔹 xs β) (suc t + (length p + listConstruction𝕋 xs)) i j ∸ length p) ∸ listConstruction𝕋 xs  ≡⟨ cong (λ v → (route𝔹 p (all𝔹 xs β) (suc t + v) i j ∸ length p) ∸ listConstruction𝕋 xs) (+-comm (length p) _) ⟩
        (route𝔹 p (all𝔹 xs β) (suc t + (listConstruction𝕋 xs + length p)) i j ∸ length p) ∸ listConstruction𝕋 xs  ≡⟨ cong (λ v → (route𝔹 p (all𝔹 xs β) v i j ∸ length p) ∸ listConstruction𝕋 xs) (≡-sym (+-assoc (suc t) _ _)) ⟩
        (route𝔹 p (all𝔹 xs β) (suc t + listConstruction𝕋 xs + length p) i j ∸ length p) ∸ listConstruction𝕋 xs    ≡⟨ cong (_∸ listConstruction𝕋 xs) (route𝔹-≈𝔹 p (all𝔹 xs β) (t + listConstruction𝕋 xs) i j) ⟩
        all𝔹 xs β (suc t + listConstruction𝕋 xs + 0) i j  ∸ listConstruction𝕋 xs                                   ≡⟨ cong (λ v → all𝔹 xs β v i j ∸ listConstruction𝕋 xs) (+-right-identity _) ⟩
        all𝔹 xs β (suc t + listConstruction𝕋 xs) i j ∸ listConstruction𝕋 xs                                        ≡⟨ all𝔹-≈𝔹 xs β t i j ⟩
        β (suc t + zero) i j
      ∎
      where open ≡-Reasoning

    all𝔹-causal : ∀ xs {β} → Causal β → Causal (all𝔹 xs β)
    all𝔹-causal []                  causal = causal
    all𝔹-causal (cnull        ∷ xs) causal = all𝔹-causal xs causal
    all𝔹-causal (croute _ p _ ∷ xs) causal = route𝔹-causal p (all𝔹-causal xs causal)

    all𝔹-dynamic : ∀ xs {β} → Dynamic β → Dynamic (all𝔹 xs β)
    all𝔹-dynamic []                  dynamic = dynamic
    all𝔹-dynamic (cnull        ∷ xs) dynamic = all𝔹-dynamic xs dynamic
    all𝔹-dynamic (croute _ p _ ∷ xs) dynamic = route𝔹-dynamic p (all𝔹-dynamic xs dynamic)
-}

    -- Schedules

    route&reset𝕊 : SimplePathⁿᵗ n → Schedule n → Schedule n
    route&reset𝕊 p 𝕤 = record
      { α              = path&reset𝔸 p α
      ; β              = path&reset𝔹 p β
      ; starvationFree = path&reset𝔸-starvationFree p starvationFree
      ; causality      = path&reset𝔹-causal p causality
      ; dynamic        = path&reset𝔹-dynamic p dynamic
      }
      where open Schedule 𝕤

{-
    all𝕊 : List CRoute → Schedule n → Schedule n
    all𝕊 xs 𝕤 = record
      { α              = all𝔸 xs α
      ; β              = all𝔹 xs β
      ; starvationFree = all𝔸-starvationFree xs starvationFree
      ; causality      = all𝔹-causal xs causality
      ; dynamic        = all𝔹-dynamic xs dynamic
      }
      where open Schedule 𝕤
  -}

    -- Results

-}
{-

    σ-route𝕊 : ∀ 𝕤 x p p∈G x≈wp → δ (route&reset𝕊 p 𝕤) (β (route&reset𝕊 r 𝕤) t i j) I {!!} {!!} ≈ᶜ r
    σ-route𝕊 = {!!}
-}

{-
    open import RoutingLib.Asynchronous.Snapshot σ-parallelisation using (Snapshot; snapshot; _≈ₛ_; toList)
-}

   
{-
    locateTime : ∀ {x xs} → x ∈ xs → 𝕋
    locateTime {_} {xs} (here  _)    = listConstruction𝕋 xs
    locateTime {_} {_}  (there x∈xs) = locateTime x∈xs

    construct𝔹 : ∀ (β : 𝔹 n) tₛ xs → (∀ {t i j} → tₛ ≤ t → β t i j ≤ tₛ → ∃ λ x → x ∈ xs) → 𝔹 n
    construct𝔹 β tₛ xs index t i j with listConstruction𝕋 xs ≤? t | β (tₛ + t ∸ listConstruction𝕋 xs) i j ≤? tₛ
    ... | yes ct≤t | yes β≤tₛ = locateTime (proj₂ (index (subst (tₛ ≤_) (≡-sym (+-∸-assoc tₛ ct≤t)) (m≤m+n tₛ (t ∸ listConstruction𝕋 xs))) β≤tₛ)) 
    ... | _        |  _       = all𝔹 xs t i j
-}

    construction𝕊 : ∀ (𝕤 : Schedule n) t → RMatrix → Snapshot (Schedule.β 𝕤) t → Schedule n
    construction𝕊 𝕤 t X snapshot = record
      { α              = construction𝔸 𝕤 t X snapshot
      ; β              = {!!}
      ; starvationFree = {!!} --all𝔸-starvationFree xs starvationFree
      ; causality      = {!!} --construct𝔹-causal xs causality
      ; dynamic        = {!!} --construct𝔹-dynamic xs dynamic
      }
      where open Schedule 𝕤

    δᵗ¹X≈δᶜᵗI : ∀ 𝕤₁ t₁ X (sn₁ : Snapshot (Schedule.β 𝕤₁) t₁) → X ≈ₘ δ (construction𝕊 𝕤₁ t₁ X sn₁) (construction𝕋 X (Schedule.dynamic 𝕤₁) sn₁) I
    δᵗ¹X≈δᶜᵗI 𝕤₁ t₁ X sn₁ = {!!}

    𝕤₁≈c𝕤 : ∀ 𝕤₁ t₁ X (sn₁ : Snapshot (Schedule.β 𝕤₁) t₁) →  𝕤₁ ⟦ t₁ ⟧≈⟦ construction𝕋 X (Schedule.dynamic 𝕤₁) sn₁ ⟧ construction𝕊 𝕤₁ t₁ X sn₁
    𝕤₁≈c𝕤 𝕤₁ t₁ X sn₁ = {!!} , {!!} 
    
    sn₁≈csn : ∀ 𝕤₁ t₁ X (sn₁ : Snapshot (Schedule.β 𝕤₁) t₁) → sn₁ ≈ₛ snapshot (construction𝕊 𝕤₁ t₁ X sn₁) (construction𝕋 X (Schedule.dynamic 𝕤₁) sn₁) I
    sn₁≈csn 𝕤₁ t₁ X sn₁ = {!!}

    reconstruct : ∀ 𝕤₁ t₁ X (sn₁ : Snapshot (Schedule.β 𝕤₁) t₁) → ∃₂ λ 𝕤₂ t₂ → X ≈ₘ δ 𝕤₂ t₂ I × 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ × sn₁ ≈ₛ snapshot 𝕤₂ t₂ I
    reconstruct 𝕤₁ t₁ X sn₁ = construction𝕊 𝕤₁ t₁ X sn₁ , construction𝕋 X dynamic sn₁ , δᵗ¹X≈δᶜᵗI 𝕤₁ t₁ X sn₁ , 𝕤₁≈c𝕤 𝕤₁ t₁ X sn₁ , sn₁≈csn 𝕤₁ t₁ X sn₁
      where open Schedule 𝕤₁
