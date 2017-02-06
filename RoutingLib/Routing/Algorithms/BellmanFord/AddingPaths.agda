open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (≤⇒pred≤)
open import Data.Vec using (Vec; _∷_; []; lookup; foldr; map; allFin)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; cong; inspect; [_]) renaming (sym to ≡-sym)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Selective)

open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SPath using ([]; [_]; lengthₚ; lengthₚ<n)
open import RoutingLib.Data.Graph.SGPath.Equivalence using ([]; _∷_; _∺_; _≃ₚ_)
open import RoutingLib.Data.Nat.Properties using (≤-refl; m<n⇨n≡o+1; m+1≤n+1⇨m≤n; ≤-trans; <⇒≤)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Asynchronous.Core
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)
import RoutingLib.Routing.Algorithms.BellmanFord
import RoutingLib.Routing.Algorithms.BellmanFord.Properties

module RoutingLib.Routing.Algorithms.BellmanFord.AddingPaths
  {a b ℓ n} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (G : Graph (RoutingAlgebra.Step ra) (suc n)) (sch : AdmissableSchedule (suc n))
  where

  open import RoutingLib.Routing.AddingSPaths.Consistent ra ⊕-sel G using (CRoute; crp; _⊕ᶜ_; _▷ᶜ_; weight; croute; cnull)
  open import RoutingLib.Routing.AddingSPaths.Inconsistent ra ⊕-sel G using (IRoute; iroute; inull; irp; _≈ⁱ_; _⊕ⁱ_; _▷ⁱ_; ▷ⁱ-pres-≈ⁱ; ≈ⁱ-reflexive; ≈ⁱ-trans; ≈ⁱ-sym)
  open import RoutingLib.Routing.AddingSPaths.Inconsistent.Properties ra ⊕-sel G using (⊕ⁱ-sel; ▷ⁱ-extensionWitness)
  open import RoutingLib.Routing.AddingSPaths.Bisimilarity ra ⊕-sel G

  open AdmissableSchedule sch
  open RoutingAlgebra ra
  open BisimilarityReasoning

  module C = Asynchronous crp sch
  module I = Asynchronous irp sch
  module IP = AsynchronousProperties irp sch


  --open RoutingProblem rp

  abstract


    Iⁱ≃Iᶜ : I.I ≃ₘ C.I
    Iⁱ≃Iᶜ i j with j ≟ᶠ i
    ... | no  _ = nullEq
    ... | yes _ = routeEq refl []


    δ'-≃ : ∀ {X Y} → X ≃ₘ Y → ∀ {t : ℕ} (acc : Acc _<_ t) → I.δ' acc X ≃ₘ C.δ' acc Y
    δ'-≃ X≃Y {zero}  (acc _) = X≃Y
    δ'-≃ X≃Y {suc t} (acc t-acc) i j with i ∈? α (suc t)
    ... | no  _ = δ'-≃ X≃Y (t-acc t ≤-refl) i j
    ... | yes _ = foldr-≃ (Iⁱ≃Iᶜ i j) {!!} --(map-≃ ? ? ?) -- (λ k → ▷-≃ i (lookup k (allFin n)) (δ'-≃ X≃Y (t-acc (β (suc t) i k) (causality t i k)) (lookup k (allFin n)) j)))

{-

    δ-≃ : ∀ {X Y} → X ≃ₘ Y → ∀ t → I.δ t X ≃ₘ C.δ t Y
    δ-≃ X≃Y t = δ'-≃ X≃Y (<-wf t)
-}

    -- Flushing


    open import RoutingLib.Asynchronous.Properties sch

    flushing-lemma : ∀ {n X i j t x p} → syncIter n ≤ t → I.δ t X i j ≈ⁱ iroute x p → lengthₚ p < n → ∃ λ cr → iroute x p ≃ cr
    flushing-lemma {zero} _ _ ()
    flushing-lemma {suc n} {X} {i} {j} {t} {x} {p} tₙ₊₁ⁱ≤t δᵗXᵢⱼ≈xp |p|<n with syncIter-activated n i
    ... | (aₜᵢ , tₙ<aₜᵢ , αₜᵢ≤tₙ₊₁ , i∈αₐₜᵢ , aₜᵢ≤s⇒tₙ≤βsij) with previousActivation-all (≤-trans αₜᵢ≤tₙ₊₁ tₙ₊₁ⁱ≤t) i∈αₐₜᵢ
    ...   | (t' , aₜᵢ≤t' , t'≤t , i∈αₜ' , t'-latestActivation) with m<n⇨n≡o+1 (≤-trans tₙ<aₜᵢ aₜᵢ≤t')
    ...     | (t'-1 , 1+t'-1≡t') with IP.δᵗ⁺¹Xᵢⱼ≈Aᵢₖ▷δᵗXₖⱼ⊎Iᵢⱼ ⊕ⁱ-sel X i j (subst (λ v → i ∈ α v) 1+t'-1≡t' i∈αₜ')
                                      | ≈ⁱ-trans (≈ⁱ-sym δᵗXᵢⱼ≈xp) (≈ⁱ-trans (IP.δᵢ-latestActivation X i j t'-latestActivation) (≈ⁱ-reflexive (cong (λ v → I.δ v X i j) 1+t'-1≡t')))
    ...       | inj₂ δᵗ'Xᵢⱼ≈Iᵢⱼ | xp≈δᵗ'Xᵢⱼ  = C.I i j , (
      begin
        iroute x p
      ≈ⁱ⟨ xp≈δᵗ'Xᵢⱼ ⟩
        I.δ (suc t'-1) X i j
      ≈ⁱ⟨ δᵗ'Xᵢⱼ≈Iᵢⱼ ⟩
        I.I i j
      ≃⟨ Iⁱ≃Iᶜ i j ⟩
        C.I i j
      ∎)
      where
    ...       | inj₁ (k , δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ) | xp≈δᵗ'Xᵢⱼ with ▷ⁱ-extensionWitness i k (I.δ (β (suc t'-1) i k) X k j) x p (≈ⁱ-sym (≈ⁱ-trans xp≈δᵗ'Xᵢⱼ δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ))
    ...         | (y , q , δβₖⱼ≈yq , |p|≡|q|+1) with flushing-lemma (<⇒≤ (aₜᵢ≤s⇒tₙ≤βsij i k aₜᵢ≤t')) (subst (λ v → I.δ (β v i k) X k j ≈ⁱ iroute y q) (≡-sym 1+t'-1≡t') δβₖⱼ≈yq) (m+1≤n+1⇨m≤n (subst (_< suc n) |p|≡|q|+1 |p|<n))
    ...           | (cr , yq≃cr) = (i , k) ▷ᶜ cr , (
      begin
        iroute x p
      ≈ⁱ⟨ xp≈δᵗ'Xᵢⱼ ⟩
        I.δ (suc t'-1) X i j
      ≈ⁱ⟨ δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ ⟩
        (i , k) ▷ⁱ (I.δ (β (suc t'-1) i k) X k j)
      ≈ⁱ⟨ ▷ⁱ-pres-≈ⁱ (i , k) δβₖⱼ≈yq ⟩
        (i , k) ▷ⁱ (iroute y q)
      ≃⟨ ▷-≃ i k yq≃cr ⟩
        (i , k) ▷ᶜ cr
      ∎)


    flushingInconsistentEntry : ∀ X i j → ∃ λ cr → I.δ (syncIter (suc n)) X i j ≃ cr
    flushingInconsistentEntry X i j with I.δ (syncIter (suc n)) X i j | inspect (I.δ (syncIter (suc n)) X i) j
    ... | inull      | _            = cnull , nullEq
    ... | iroute x p | [ δˢⁱⁿXᵢⱼ≡xp ] = flushing-lemma ≤-refl (≈ⁱ-reflexive δˢⁱⁿXᵢⱼ≡xp) (lengthₚ<n p)

    flushInconsistencies : ∀ X → ∃ λ Y → I.δ (syncIter (suc n)) X ≃ₘ Y
    flushInconsistencies X = (λ i j → proj₁ (flushingInconsistentEntry X i j)) , (λ i j → proj₂ (flushingInconsistentEntry X i j))
