open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset using (Subset; _∈_; ⁅_⁆)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _+_; ≤-pred)
open import Data.Nat.Properties using (≤⇒pred≤; n≤m+n; <-trans)
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Vec using (Vec; _∷_; []; lookup; foldr; map; allFin)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Level using (_⊔_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; cong; inspect; [_]; module ≡-Reasoning) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Selective)

open import RoutingLib.Asynchronous.Properties using ()
open import RoutingLib.Asynchronous.Snapshot using (Snapshot; snapshot)
open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Properties using (≈𝔸-refl)
open import RoutingLib.Asynchronous.Schedule.Times using (pseudoperiod𝔸)
open import RoutingLib.Asynchronous.Schedule.Times.Properties using (pseudoperiod𝔸-all; pseudoperiod𝔸-inc; previousActivation-all)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∷_; _∺_; _∷_∣_; _∺_∣_; length; source)
open import RoutingLib.Data.Graph.SimplePath.Properties using (length<n)
open import RoutingLib.Data.Nat.Properties using (≤-refl; m<n⇨n≡o+1; ≤-trans; <⇒≤)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)

module RoutingLib.Routing.Algorithms.BellmanFord.AddingPaths
  {a b ℓ n-1} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (G : Graph (RoutingAlgebra.Step ra) (suc n-1))
  where

  open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G using (CRoute; crp; _⊕ᶜ_; _▷ᶜ_; weight; croute; cnull; ≈ᶜ-sym)
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent ra ⊕-sel G using (IRoute; iroute; inull; irp; _≈ⁱ_; _⊕ⁱ_; _▷ⁱ_; ▷ⁱ-pres-≈ⁱ; ≈ⁱ-reflexive; ≈ⁱ-trans; ≈ⁱ-sym; size)
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent.Properties ra ⊕-sel G using (⊕ⁱ-sel; ▷ⁱ-extensionWitness; ▷ⁱ-size; x≈y⇒|x|≡|y|)
  open import RoutingLib.Routing.AlgebraicPaths.Bisimilarity ra ⊕-sel G
  open import RoutingLib.Routing.Algorithms.BellmanFord.StateReconstruction ra ⊕-sel G using (reconstructionAll)

  open RoutingAlgebra ra
  open BisimilarityReasoning

  import RoutingLib.Routing.Algorithms.BellmanFord as BellmanFord
  import RoutingLib.Routing.Algorithms.BellmanFord.Properties as BellmanFordProperties
  module C  = BellmanFord crp
  module I  = BellmanFord irp
  module IP = BellmanFordProperties irp

  private
    
    n : ℕ
    n = suc n-1

    n+2 : ℕ
    n+2 = suc (suc n)
      
    size<n : ∀ r → size r < n
    size<n inull        = s≤s z≤n
    size<n (iroute _ p) = length<n p


  _≃ₛ_ : ∀ {β₁ β₂ : 𝔹 n} {t₁ t₂ : 𝕋} → Snapshot (I.σ∥) β₁ t₁ → Snapshot (C.σ∥) β₂ t₂ → Set (a ⊔ b ⊔ ℓ)
  _≃ₛ_ {β₁} {β₂} {t₁} {t₂} s₁ s₂ = ∀ t i j k (βᵢⱼ≤t₁ : β₁ (t + t₁) i j ≤ t₁) (βᵢⱼ≤t₂ : β₂ (t + t₂) i j ≤ t₂) → s₁ i j (n≤m+n t t₁) βᵢⱼ≤t₁ k ≃ s₂ i j (n≤m+n t t₂) βᵢⱼ≤t₂ k



  abstract

    Iⁱ≃Iᶜ : I.I ≃ₘ C.I
    Iⁱ≃Iᶜ i j with j ≟ᶠ i
    ... | no  _ = nullEq
    ... | yes _ = routeEq refl []

{-
    δ'-≃ : ∀ {X Y} → X ≃ₘ Y → ∀ {t : ℕ} (acc : Acc _<_ t) → I.δ' acc X ≃ₘ C.δ' acc Y
    δ'-≃ X≃Y {zero}  (acc _) = X≃Y
    δ'-≃ X≃Y {suc t} (acc t-acc) i j with i ∈? α (suc t)
    ... | no  _ = δ'-≃ X≃Y (t-acc t ≤-refl) i j
    ... | yes _ = foldr-≃ (Iⁱ≃Iᶜ i j) {!!} --(map-≃ ? ? ?) -- (λ k → ▷-≃ i (lookup k (allFin n)) (δ'-≃ X≃Y (t-acc (β (suc t) i k) (causality t i k)) (lookup k (allFin n)) j)))
-}

    postulate δ-≃ : ∀ 𝕤 {X Y} → X ≃ₘ Y → ∀ t → I.δ 𝕤 t X ≃ₘ C.δ 𝕤 t Y


    --δ-≃ X≃Y t = δ'-≃ X≃Y (<-wf t)

    -- Flushing


    --open import RoutingLib.Asynchronous.Properties σ-parallelisation 𝕤

    open Schedule

    flushing-lemma : ∀ 𝕤 {n X i j t} → pseudoperiod𝔸 𝕤 n ≤ t → size (I.δ 𝕤 t X i j) < n → ∃ λ cr → I.δ 𝕤 t X i j ≃ cr
    flushing-lemma 𝕤 {zero} _ ()
    flushing-lemma 𝕤 {suc n} {X} {i} {j} {t} tₙ₊₁ⁱ≤t |p|<n with pseudoperiod𝔸-all 𝕤 n i
    ... | (aₜᵢ , tₙ<aₜᵢ , αₜᵢ≤tₙ₊₁ , i∈αₐₜᵢ , aₜᵢ≤s⇒tₙ≤βsij) with previousActivation-all (starvationFree 𝕤) (≤-trans αₜᵢ≤tₙ₊₁ tₙ₊₁ⁱ≤t) i∈αₐₜᵢ
    ...   | (t' , aₜᵢ≤t' , t'≤t , i∈αₜ' , t'-latestActivation) with m<n⇨n≡o+1 (≤-trans tₙ<aₜᵢ aₜᵢ≤t')
    ...     | (t'-1 , t'≡1+t'-1) rewrite t'≡1+t'-1 with IP.δᵗ⁺¹Xᵢⱼ≈Aᵢₖ▷δᵗXₖⱼ⊎Iᵢⱼ 𝕤 ⊕ⁱ-sel X i∈αₜ' j | IP.δ-constantSinceActivation 𝕤 X i t'≤t t'-latestActivation j
    ...       | inj₂ δᵗ'Xᵢⱼ≈Iᵢⱼ           | δᵗX≈δᵗ'X = C.I i j , ic+ii⇒ic (Iⁱ≃Iᶜ i j) (≈ⁱ-sym (≈ⁱ-trans δᵗX≈δᵗ'X δᵗ'Xᵢⱼ≈Iᵢⱼ))
    ...       | inj₁ (k , δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ) | δᵗX≈δᵗ'X with I.δ 𝕤 (suc t'-1) X i j | inspect (I.δ 𝕤 (suc t'-1) X i) j
    ...         | inull      | [ δt'X≡inull ] = cnull , ic+ii⇒ic nullEq (≈ⁱ-sym δᵗX≈δᵗ'X)
    ...         | iroute x p | [ δᵗ'X≡xp ] with flushing-lemma 𝕤 (<⇒≤ (aₜᵢ≤s⇒tₙ≤βsij k aₜᵢ≤t')) (≤-pred (subst (_< suc n) (≡-trans (x≈y⇒|x|≡|y| (≈ⁱ-trans δᵗX≈δᵗ'X δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ)) (▷ⁱ-size (I.δ 𝕤 (β 𝕤 (suc t'-1) i k) X k j) (≈ⁱ-sym δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ))) |p|<n))
    ...           | (cr , δβₖⱼ≃cr) = (i , k) ▷ᶜ cr ,
      (begin
        I.δ 𝕤 t X i j                                  ≈ⁱ⟨ IP.δ-constantSinceActivation 𝕤 X i t'≤t t'-latestActivation j ⟩
        I.δ 𝕤 (suc t'-1) X i j                         ≈ⁱ⟨ ≈ⁱ-trans (≈ⁱ-reflexive δᵗ'X≡xp) δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ ⟩
        (i , k) ▷ⁱ (I.δ 𝕤 (β 𝕤 (suc t'-1) i k) X k j)  ≃⟨ ▷-≃ (i , k) δβₖⱼ≃cr ⟩
        (i , k) ▷ᶜ cr
      ∎)

    --------------------
    -- Reconstruction --
    --------------------

    cₜ : Schedule n → ℕ
    cₜ 𝕤 = pseudoperiod𝔸 𝕤 (suc n)

    consistentStateAt-cₜ : ∀ 𝕤 X i j → ∃ λ cr → I.δ 𝕤 (cₜ 𝕤) X i j ≃ cr
    consistentStateAt-cₜ 𝕤 X i j = flushing-lemma 𝕤 (<⇒≤ (pseudoperiod𝔸-inc 𝕤 n)) (size<n (I.δ 𝕤 (cₜ 𝕤) X i j))

    stateAt-cₜ : Schedule n → I.RMatrix → C.RMatrix
    stateAt-cₜ 𝕤 X i j = proj₁ (consistentStateAt-cₜ 𝕤 X i j)

    consistentMessagesAt-cₜ : ∀ 𝕤 X i j k {t'} (cₜ≤t' : cₜ 𝕤 ≤ t') βt'≤cₜ → ∃ λ cr → snapshot I.σ∥ 𝕤 (cₜ 𝕤) X i j cₜ≤t' βt'≤cₜ k ≃ cr
    consistentMessagesAt-cₜ 𝕤 X i j k {t'} cₜ≤t' βt'≤cₜ with pseudoperiod𝔸-all 𝕤 n i
    ... | (t'' , ppₙ<t'' , t''≤ppₙ₊₁ , i∈αt'' , ppₙ<βt'') = flushing-lemma 𝕤 (<⇒≤ (ppₙ<βt'' j (≤-trans t''≤ppₙ₊₁ cₜ≤t'))) (size<n (I.δ 𝕤 (β 𝕤 t' i j) X j k))

    messagesAt-cₜ : ∀ 𝕤 → I.RMatrix → Snapshot C.σ∥ (β 𝕤) (cₜ 𝕤)
    messagesAt-cₜ 𝕤 X {t'} i j cₜ≤t' βt'≤cₜ k = proj₁ (consistentMessagesAt-cₜ 𝕤 X i j k cₜ≤t' βt'≤cₜ)

    convergeToConsistency : ∀ 𝕤₁ X → ∃₂ λ t₁ t₂ → ∃ λ 𝕤₂ → I.δ 𝕤₁ t₁ X ≃ₘ C.δ 𝕤₂ t₂ C.I × 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ × snapshot I.σ∥ 𝕤₁ t₁ X ≃ₛ snapshot C.σ∥ 𝕤₂ t₂ C.I
    convergeToConsistency 𝕤₁ X with reconstructionAll 𝕤₁ (cₜ 𝕤₁) (stateAt-cₜ 𝕤₁ X) (messagesAt-cₜ 𝕤₁ X)
    ... | (𝕤₂ , t₂ , δᶜᵗX≈δᵗ²I , 𝕤₁≈𝕤₂ , z) = 
      cₜ 𝕤₁ , 
      t₂ , 
      𝕤₂ , 
      (λ i j → ic+cc⇒ic (proj₂ (consistentStateAt-cₜ 𝕤₁ X i j)) (≈ᶜ-sym (δᶜᵗX≈δᵗ²I i j))) , 
      𝕤₁≈𝕤₂ , 
      (λ t i j k β≤cₜ β≤t₂ → ic+cc⇒ic (proj₂ (consistentMessagesAt-cₜ 𝕤₁ X i j k (n≤m+n t (cₜ 𝕤₁)) β≤cₜ)) (≈ᶜ-sym (z t i j β≤cₜ β≤t₂ k)))


    postulate ≃ₛ⇒≃ₘ : ∀ {𝕤₁ 𝕤₂ t₁ t₂} X₁ X₂ → 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ → snapshot I.σ∥ 𝕤₁ t₁ X₁ ≃ₛ snapshot C.σ∥ 𝕤₂ t₂ X₂ → 
                I.δ 𝕤₁ t₁ X₁ ≃ₘ C.δ 𝕤₂ t₂ X₂ → ∀ t → I.δ 𝕤₁ (t + t₁) X₁ ≃ₘ C.δ 𝕤₂ (t + t₂) X₂
