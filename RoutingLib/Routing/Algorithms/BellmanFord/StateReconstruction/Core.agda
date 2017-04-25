open import Level using (_⊔_)
open import Algebra.FunctionProperties using (Selective)
open import Data.List using (List; []; _∷_; _++_; sum; map; foldr; concat)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (≤-step; _+-mono_; m≤m+n; n≤m+n)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Any using (here; there)
open import Data.List.All using (All; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (_Preserves_⟶_; _Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂) renaming (refl to ≡-refl)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (setoid to Lₛ; Rel to ListRel)
open import Function using (_∘_)

open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Times using (expiryᵢⱼ)
open import RoutingLib.Asynchronous.Schedule.Times.Properties using (expiryᵢⱼ-expired)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∷_; _∷_∣_; _∺_∣_; length)
open import RoutingLib.Data.Graph.SimplePath.Properties using (∈𝔾-resp-≈)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties using () renaming (∉-resp-≈ to ∉ₚ-resp-≈ₚ)
open import RoutingLib.Routing.Definitions using (RoutingAlgebra; RoutingProblem)
open import RoutingLib.Data.List using (tabulate; decFilter)
open import RoutingLib.Data.List.Properties using (tabulate-cong)
open import RoutingLib.Data.List.All.Properties using (all-decFilter)
open import RoutingLib.Data.List.Any.GenericMembership using (∈-concat; ∈-tabulate; ∈-map; ∈-++ₗ; ∈-++ᵣ; ∈-decFilter)
open import RoutingLib.Data.Nat.Properties using (≤-refl; _<?_; ≮⇒≥; <⇒≱; ≤+≢⇒<; <-irrefl; ≤-trans; ≤-reflexive; ≤-cardinality; m≤n⇒m≤o+n; m≤n⇒m≤n+o; +-comm)

module RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction.Core
  {a b ℓ n-1} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (G : Graph (RoutingAlgebra.Step ra) (suc n-1))
  where

  private

    open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G
    open import RoutingLib.Routing.Algorithms.BellmanFord crp using (σ∥)
    open RoutingProblem crp using (RMatrix; _≈ₜ_; Sₜ)
    open import RoutingLib.Asynchronous.Snapshot σ∥ using (Snapshot; toListⱼ; _≈ₛ_; snapshot)
    open import RoutingLib.Data.List.Any.GenericMembership Cₛ using (_∈_)
    
    n : ℕ
    n = suc n-1

  -------------------
  -- Current state --
  -------------------
  -- At reconstruction time we need to be able to build every CRoute in the current state.
  --  # The 0# (cnull) or 1# (croute 1 []) elements are trivial to recreate
  --  # Likewise CRoutes with paths of length 1 can be immediately recreated in a single time step
  --  # For all other "non-trivial" CRoutes we need to build the first part of them in advance
  --    i.e. for any CRoute with the path of the form [ i∷p ] we will need to generate path [ p ]
  --    ahead of time so that [ i∷p ] can be formed at the correct point in time in the new schedule.

  -- A type denoting the fact that an entry in the current routing state is non trivial and needs to be constructed.
  data NonTrivialState : CRoute → Set (a ⊔ ℓ) where
    ntState   : ∀ {x i p} i∉p i∷p∈G x≈w[i∷p] → NonTrivialState (croute x [ i ∷ p ∣ i∉p ] i∷p∈G x≈w[i∷p])

  nonTrivialState? : Decidable NonTrivialState
  nonTrivialState? cnull                                     = no λ()
  nonTrivialState? (croute _ []              _     _)        = no λ()
  nonTrivialState? (croute _ [ _ ∺ _ ∣ _ ]   _     _)        = no λ()
  nonTrivialState? (croute _ [ _ ∷ _ ∣ i∉p ] i∷p∈G x≈w[i∷p]) = yes (ntState i∉p i∷p∈G x≈w[i∷p])

  nonTrivialState-resp-≈ᶜ : NonTrivialState Respects _≈ᶜ_
  nonTrivialState-resp-≈ᶜ (crouteEq _ [ ≡-refl ∷ _ ]) (ntState _ _ _) = ntState _ _ _


  -- List of CRoutes in the current state
  states : RMatrix → List CRoute
  states X = concat (map tabulate (tabulate X))

  ∈-states : ∀ X i j → X i j ∈ states X
  ∈-states X i j = ∈-concat Cₛ (∈-tabulate Cₛ (X i) j) (∈-map (Lₛ Cₛ) Sₜ (tabulate-cong _ _) (∈-tabulate Sₜ X i))


  -- List of non-trivial CRoutes in the current state
  nonTrivialStates : RMatrix → List CRoute
  nonTrivialStates X = decFilter nonTrivialState? (states X)

  ∈-nonTrivialStates : ∀ X i j → NonTrivialState (X i j) → X i j ∈ nonTrivialStates X
  ∈-nonTrivialStates X i j nt = ∈-decFilter Cₛ nonTrivialState? nonTrivialState-resp-≈ᶜ nt (∈-states X i j)

  all-nonTrivialStates : ∀ X → All NonTrivialState (nonTrivialStates X)
  all-nonTrivialStates X = all-decFilter nonTrivialState? (states X)


  -- The amount of time needed to generate the precursor information necessary to reconstruct the current state
  -- (for a path [ i∷p ] we need: |p| (to construct p) + 1 (to reset the state after) = |i∷p|
  state𝕋 : RMatrix → 𝕋
  state𝕋 X = sum (map size (nonTrivialStates X))


  -- For a given non-trivial state in a list of such states returns the time in the new schedule at which its precursor can be found
  indexNonTrivialStates : ∀ {xs} → All NonTrivialState xs → ∀ {x} → x ∈ xs → 𝕋
  indexNonTrivialStates {_ ∷ xs} ((ntState {p = p} _ _ _) ∷ _) (here _)     = sum (map size xs) + length [ p ]
  indexNonTrivialStates {_ ∷ _}  (_ ∷ pxs)                     (there x∈xs) = indexNonTrivialStates pxs x∈xs

  indexNTStates≤state𝕋 : ∀ {xs} xs-all → ∀ {x} → (x∈xs : x ∈ xs) → indexNonTrivialStates xs-all x∈xs ≤ sum (map size xs)
  indexNTStates≤state𝕋 {_ ∷ xs} ((ntState _ _ _) ∷ _) (here _)     = ≤-step (≤-reflexive (+-comm (sum (map size xs)) _))
  indexNTStates≤state𝕋 {x ∷ xs} (_ ∷ pxs)             (there x∈xs) = m≤n⇒m≤o+n (size x) (indexNTStates≤state𝕋 pxs x∈xs)


  -- For a given non-trivial Xᵢⱼ returns the time in the new schedule at which its precursor can be found
  indexState : RMatrix → Fin n → Fin n → 𝕋
  indexState X i j with nonTrivialState? (X i j)
  ... | no _      = zero
  ... | yes Xᵢⱼ-nt = indexNonTrivialStates (all-nonTrivialStates X) (∈-nonTrivialStates X i j Xᵢⱼ-nt)

  indexState≤state𝕋 : ∀ X i j → indexState X i j ≤ state𝕋 X
  indexState≤state𝕋 X i j with nonTrivialState? (X i j)
  ... | no _      = z≤n
  ... | yes Xᵢⱼ-nt = indexNTStates≤state𝕋 (all-nonTrivialStates X) (∈-nonTrivialStates X i j Xᵢⱼ-nt)


  ------------------------
  -- Messages in flight --
  ------------------------
  -- At reconstruction time we need the exact same set of messages in flight and therefore we need to 
  -- generate these messages ahead of time:
  --  # The 0# (cnull) or 1# (croute 1 []) elements are trivial to recreate
  --  # For all other "non-trivial" CRoutes we need to build them in advance i.e. for any CRoute
  --    with a path of the form [ p ] we will need to generate path [ p ] ahead of time so that
  --    the message can be in flight at the correct point in time in the new schedule.

  -- A type denoting the fact that a message in flight is non trivial and needs to be constructed.
  data NonTrivialMessage : CRoute → Set (a ⊔ ℓ) where
    ntMessage : ∀ {x p} p∈G x≈w[p] → NonTrivialMessage (croute x [ p ] p∈G x≈w[p])

  nonTrivialMessage? : Decidable NonTrivialMessage
  nonTrivialMessage? cnull                       = no λ()
  nonTrivialMessage? (croute _ []    _   _)      = no λ()
  nonTrivialMessage? (croute _ [ p ] p∈G x≈w[p]) = yes (ntMessage p∈G x≈w[p])
  
  nonTrivialMessage-resp-≈ᶜ : NonTrivialMessage Respects _≈ᶜ_
  nonTrivialMessage-resp-≈ᶜ (crouteEq _ [ _ ]) (ntMessage _ _) = ntMessage _ _


  -- List of CRoute messages in flight from i to j at time tₛ that are received strictly before time t
  messagesᵢⱼ-bounded : ∀ {β tₛ} → Snapshot β tₛ → 𝕋 → Fin n → Fin n → List CRoute
  messagesᵢⱼ-bounded {β} {tₛ} sn zero    i j = []
  messagesᵢⱼ-bounded {β} {tₛ} sn (suc t) i j with tₛ ≤? t | β t i j ≤? tₛ
  ... | no _     | _       = []
  ... | _        | no  _   = messagesᵢⱼ-bounded sn t i j
  ... | yes tₛ≤t | yes β≤tₛ = sn i j tₛ≤t β≤tₛ j ∷ messagesᵢⱼ-bounded sn t i j

  ∈-messagesᵢⱼ-bounded : ∀ {β tₛ} (dyn : Dynamic β) (sn : Snapshot β tₛ) i j tᶠ t' (tₛ≤t' : tₛ ≤ t') (t'<tᶠ : t' < tᶠ) (β≤tₛ : β t' i j ≤ tₛ) → sn i j tₛ≤t' β≤tₛ j ∈ messagesᵢⱼ-bounded sn tᶠ i j
  ∈-messagesᵢⱼ-bounded {β} {tₛ} dyn sn i j (suc tᶠ) t' tₛ≤t' (s≤s t'≤tᶠ) βt'≤tₛ with t' ≟ tᶠ | tₛ ≤? tᶠ | β tᶠ i j ≤? tₛ
  ... | _          | no  tₛ≰t' | _         = contradiction (≤-trans tₛ≤t' t'≤tᶠ) tₛ≰t'
  ... | yes ≡-refl | yes _     | no βt'≰tₛ = contradiction βt'≤tₛ βt'≰tₛ
  ... | yes ≡-refl | yes _     | yes _     = here (≈ᶜ-reflexive (cong₂ (λ tₛ≤t' β≤tₛ → sn i j tₛ≤t' β≤tₛ j) (≤-cardinality _ _) (≤-cardinality _ _)))
  ... | no  t'≢tᶠ   | yes _    | no  _     = ∈-messagesᵢⱼ-bounded dyn sn i j tᶠ t' tₛ≤t' (≤+≢⇒< t'≤tᶠ t'≢tᶠ) βt'≤tₛ
  ... | no  t'≢tᶠ   | yes tₛ≤t | yes β≤tₛ   = there (∈-messagesᵢⱼ-bounded dyn sn i j tᶠ t' tₛ≤t' (≤+≢⇒< t'≤tᶠ t'≢tᶠ) βt'≤tₛ)


  -- List of CRoute messages in flight from i to j at time tₛ
  messagesᵢⱼ : ∀ {β tₛ} → Dynamic β → Snapshot β tₛ → Fin n → Fin n → List CRoute
  messagesᵢⱼ {_} {tₛ} dyn sn i j = messagesᵢⱼ-bounded sn (expiryᵢⱼ dyn tₛ i j) i j

  ∈-messagesᵢⱼ : ∀ {β t} dyn (sn : Snapshot β t) i j t' (t≤t' : t ≤ t') (β≤t : β t' i j ≤ t) → sn i j t≤t' β≤t j ∈ messagesᵢⱼ dyn sn i j
  ∈-messagesᵢⱼ {_} {tₛ} dyn sn i j t' t≤t' β≤t with t' <? expiryᵢⱼ dyn tₛ i j
  ... | yes t'<exp = ∈-messagesᵢⱼ-bounded dyn sn i j (expiryᵢⱼ dyn tₛ i j) t' t≤t' t'<exp β≤t
  ... | no  t'≮exp = contradiction (expiryᵢⱼ-expired dyn tₛ i j (≮⇒≥ t'≮exp)) (<⇒≱ (s≤s β≤t))


  -- List of CRoute messages in flight from i at time tₛ
  messagesᵢ : ∀ {β tₛ} → Dynamic β → Snapshot β tₛ → Fin n → List CRoute
  messagesᵢ dyn sn i = concat (tabulate (messagesᵢⱼ dyn sn i))

  ∈-messagesᵢ : ∀ {β t} dyn (sn : Snapshot β t) i j t' (t≤t' : t ≤ t') (β≤t : β t' i j ≤ t) → sn i j t≤t' β≤t j ∈ messagesᵢ dyn sn i
  ∈-messagesᵢ dyn sn i j t' t≤t' β≤t = ∈-concat Cₛ (∈-messagesᵢⱼ dyn sn i j t' t≤t' β≤t) (∈-tabulate (Lₛ Cₛ) (messagesᵢⱼ dyn sn i) j)


  -- List of CRoute messages in flight at time tₛ
  messages : ∀ {β t} → Dynamic β → Snapshot β t → List CRoute
  messages dyn sn = concat (tabulate (messagesᵢ dyn sn))

  ∈-messages : ∀ {β t} dyn (sn : Snapshot β t) i j t' (t≤t' : t ≤ t') (β≤t : β t' i j ≤ t) → sn i j t≤t' β≤t j ∈ messages dyn sn
  ∈-messages dyn sn i j t' t≤t' β≤t = ∈-concat Cₛ (∈-messagesᵢ dyn sn i j t' t≤t' β≤t) (∈-tabulate (Lₛ Cₛ) (messagesᵢ dyn sn) i)


  -- List of non-trivial CRoute messages in flight at time tₛ
  nonTrivialMessages : ∀ {β t} → Dynamic β → Snapshot β t → List CRoute
  nonTrivialMessages dyn sn = decFilter nonTrivialMessage? (messages dyn sn)

  ∈-nonTrivialMessages : ∀ {β t} dyn (sn : Snapshot β t) i j t' (t≤t' : t ≤ t') (β≤t : β t' i j ≤ t) → NonTrivialMessage (sn i j t≤t' β≤t j) → sn i j t≤t' β≤t j ∈ nonTrivialMessages dyn sn
  ∈-nonTrivialMessages dyn sn i j t' t≤t' β≤t nt = ∈-decFilter Cₛ nonTrivialMessage? nonTrivialMessage-resp-≈ᶜ nt (∈-messages dyn sn i j t' t≤t' β≤t)

  all-nonTrivialMessages : ∀ {β t} dyn (sn : Snapshot β t) → All NonTrivialMessage (nonTrivialMessages dyn sn)
  all-nonTrivialMessages dyn sn = all-decFilter nonTrivialMessage? (messages dyn sn)


  -- The amount of time needed to reconstruct the messages in flight
  -- (for a path [ p ] we need: |p| (to construct p) + 1 (to reset the state after) = |p|+1
  messages𝕋 : ∀ {β t} → Dynamic β → Snapshot β t → 𝕋
  messages𝕋 dyn sn = sum (map (suc ∘ size) (nonTrivialMessages dyn sn))

  -- For a given non-trivial message returns the time in the new schedule at which it can be found
  indexNonTrivialMessage : ∀ {xs} → All NonTrivialMessage xs → ∀ {x} → x ∈ xs → 𝕋
  indexNonTrivialMessage {x ∷ xs} (ntMessage _ _ ∷ pxs) (here _)     = sum (map (suc ∘ size) xs) + size x
  indexNonTrivialMessage {_ ∷ _}  (_ ∷ pxs)             (there x∈xs) = indexNonTrivialMessage pxs x∈xs

  indexNonTrivialMessages≤messages𝕋 : ∀ {xs} xs-all → ∀ {x} → (x∈xs : x ∈ xs) → indexNonTrivialMessage xs-all x∈xs ≤ sum (map (suc ∘ size) xs)
  indexNonTrivialMessages≤messages𝕋 {_ ∷ xs} (ntMessage _ _ ∷ xs-all) (here px₁)   = ≤-step (≤-reflexive (+-comm (sum (map (suc ∘ size) xs)) _))
  indexNonTrivialMessages≤messages𝕋 {x ∷ _}  (px ∷ xs-all)            (there x∈xs) = m≤n⇒m≤o+n (suc (size x)) (indexNonTrivialMessages≤messages𝕋 xs-all x∈xs)

  -- For a given message returns the time in the new schedule at which it can be found
  indexMessage : RMatrix → ∀ {β tₛ} → Dynamic β → (sn : Snapshot β tₛ) → ∀ i j t → tₛ ≤ t → β t i j ≤ tₛ → 𝕋
  indexMessage X dyn sn i j t tₛ≤t βt≤tₛ with nonTrivialMessage? (sn i j tₛ≤t βt≤tₛ j)
  ... | no _   = zero
  ... | yes nt = state𝕋 X + indexNonTrivialMessage (all-nonTrivialMessages dyn sn) (∈-nonTrivialMessages dyn sn i j t tₛ≤t βt≤tₛ nt)

  indexMessage≤state𝕋+messages𝕋 : ∀ X {β tₛ} dyn (sn : Snapshot β tₛ) i j t tₛ≤t βt≤tₛ → indexMessage X dyn sn i j t tₛ≤t βt≤tₛ ≤ state𝕋 X + messages𝕋 dyn sn
  indexMessage≤state𝕋+messages𝕋 X dyn sn i j t tₛ≤t βt≤tₛ with nonTrivialMessage? (sn i j tₛ≤t βt≤tₛ j)
  ... | no  _  = z≤n
  ... | yes nt = (≤-refl {state𝕋 X} +-mono indexNonTrivialMessages≤messages𝕋 (all-nonTrivialMessages dyn sn) (∈-nonTrivialMessages dyn sn i j t tₛ≤t βt≤tₛ nt))


  -----------
  -- Other --
  -----------

  -- The time required to build a schedule that builds the provided state and the provided messages
  build𝕋 : RMatrix → ∀ {β tₛ} → Dynamic β → Snapshot β tₛ → 𝕋
  build𝕋 X dyn sn = suc (state𝕋 X + messages𝕋 dyn sn)
  
  state𝕋<build𝕋 : ∀ X {β tₛ} dyn (sn : Snapshot β tₛ) → state𝕋 X < build𝕋 X dyn sn
  state𝕋<build𝕋 X dyn sn = s≤s (m≤m+n _ _)

  indexState<build𝕋 : ∀ X {β tₛ} dyn (sn : Snapshot β tₛ) i j → indexState X i j < build𝕋 X dyn sn
  indexState<build𝕋 X dyn sn i j = ≤-trans (s≤s (indexState≤state𝕋 X i j)) (state𝕋<build𝕋 X dyn sn)

  messages𝕋<build𝕋 : ∀ X {β tₛ} dyn (sn : Snapshot β tₛ) → messages𝕋 dyn sn < build𝕋 X dyn sn
  messages𝕋<build𝕋 X dyn sn = s≤s (n≤m+n (state𝕋 X) _)

  indexMessage<build𝕋 : ∀ X {β tₛ} dyn (sn : Snapshot β tₛ) i j t tₛ≤t βt≤tₛ → indexMessage X dyn sn i j t tₛ≤t βt≤tₛ < build𝕋 X dyn sn
  indexMessage<build𝕋 X dyn sn i j t tₛ≤t βt≤tₛ = s≤s (indexMessage≤state𝕋+messages𝕋 X dyn sn i j t tₛ≤t βt≤tₛ)
  

  -- Abstract versions of build𝕋 (for performance reasons)
  abstract

    build𝕋𝔸 : RMatrix → ∀ {β t} → Dynamic β → Snapshot β t → 𝕋
    build𝕋𝔸 = build𝕋

    build𝕋𝔸-≡ : build𝕋 ≡ build𝕋𝔸
    build𝕋𝔸-≡ = ≡-refl


{-
    completeList𝔸 : ∀ {β t} → RMatrix → Dynamic β → Snapshot β t → List CRoute
    completeList𝔸 = completeList

    completeList𝔸-≡ : ∀ {β t} X dyn (sn : Snapshot β t) → completeList X dyn sn ≡ completeList𝔸 X dyn sn
    completeList𝔸-≡ X dyn sn = refl

-}
