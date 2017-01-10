open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; zero; s≤s; z≤n; _+_) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤-step)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (∄; ∃; _×_; _,_; proj₁)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe using (just; nothing; Eq)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel; IsDecEquivalence; Transitive; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; inspect; [_]; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties using (Op₂; Idempotent; Associative; Commutative; RightIdentity; RightZero)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Algebra.FunctionProperties using (Selective)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Nat.Properties using (≤-stepdown) renaming (≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import RoutingLib.Data.Graph using (Graph; _ᵉ∈ᵍ_; _ᵉ∈ᵍ?_)
open import RoutingLib.Data.Graph.EGPath hiding (weight)
open import RoutingLib.Data.Graph.EGPath.Properties
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.ConvergenceConditions


module RoutingLib.Routing.AddingPaths.Consistent.ConvergenceConditionProperties
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  (cc : ConvergenceConditionsWithPaths ra)
  where

  open RoutingAlgebra ra
  open ConvergenceConditionsWithPaths cc

  
  open import RoutingLib.Routing.AddingPaths.Consistent ra ⊕-sel one G
  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord crp
  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties crp
  open import RoutingLib.Routing.AddingPaths.Consistent.PathAlignment ra ⊕-sel one G

  open import RoutingLib.Routing.AddingPaths.Consistent.Properties ra ⊕-sel one G renaming (
       ⊕ᶜ-assoc to ⊕ᶜ-assoc'; 
       ⊕ᶜ-sel to ⊕ᶜ-sel'; 
       ⊕ᶜ-comm to ⊕ᶜ-comm'; 
       ⊕ᶜ-almost-strictly-absorbs-▷ᶜ to ⊕ᶜ-almost-strictly-absorbs-▷ᶜ'; 
       cnull-idᵣ-⊕ᶜ to cnull-idᵣ-⊕ᶜ'; 
       cnull-anᵣ-▷ᶜ to cnull-anᵣ-▷ᶜ'; 
       Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ to Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ'
    )
  
  convergenceConditions : ConvergenceConditions crp 
  convergenceConditions = record { 
       ⊕-assoc = ⊕ᶜ-assoc' ⊕-comm ⊕-assoc; 
       ⊕-sel = ⊕ᶜ-sel'; 
       ⊕-comm = ⊕ᶜ-comm' ⊕-comm; 
       ⊕-almost-strictly-absorbs-▷ = ⊕ᶜ-almost-strictly-absorbs-▷ᶜ' ⊕-absorbs-▷;
       0# = cnull;
       0#-idᵣ-⊕ = cnull-idᵣ-⊕ᶜ'; 
       0#-anᵣ-▷ = cnull-anᵣ-▷ᶜ';
       Iᵢⱼ≈0# = λ j≢i → ≈ᶜ-reflexive (Iᶜᵢⱼ≡cnull j≢i);
       Iᵢᵢ-almost-anᵣ-⊕ = Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ' one-anᵣ-⊕; 
       routes-enumerable = ≈ᶜ-enumerable
    }

  open ConvergenceConditions convergenceConditions renaming (
       ⊕-assoc to ⊕ᶜ-assoc; 
       ⊕-sel to ⊕ᶜ-sel; 
       ⊕-comm to ⊕ᶜ-comm; 
       ⊕-almost-strictly-absorbs-▷ to ⊕ᶜ-almost-strictly-absorbs-▷ᶜ; 
       Iᵢⱼ-idᵣ-⊕ to Iᶜᵢⱼ-idᵣ-⊕ᶜ; 
       Iᵢⱼ-anᵣ-▷ to Iᶜᵢⱼ-anᵣ-▷ᶜ ; 
       Iᵢᵢ-almost-anᵣ-⊕ to Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ
     ) public 

  --open import Relation.Binary.PartialOrderReasoning ≤-poset


{-
  ∃p⇨σᵖₚₚ≈xq : ∀ (p : EGPath G) → ∀ X → DiagonalAligned X → ∃ λ (q : EGPath G) → σ^ (length p) X (source p) (destination p) ≈ᶜ croute (weight q) q refl × length q ≤ℕ length p
  ∃p⇨σᵖₚₚ≈xq [ i ]                      X Xda = [ i ] , Xda i , z≤n --≈ᶜ-trans (σXᵢᵢ≈Iᵢᵢ ⊕ᶜ-sel Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ X i) (≈ᶜ-reflexive (Iᶜᵢᵢ≡one[i] i)) , z≤n
  ∃p⇨σᵖₚₚ≈xq (i ∷ p ∣ i∉j ∣ (v , eᵢⱼ≡v))  X Xda with ∃p⇨σᵖₚₚ≈xq p X Xda
  ... | (q , σᵖₚₚ≈q , |q|≤|p|) with i ∉? q
  ...   | yes i∉q = {!!}
  ...   | no  i∈q = {!!}
-}

  -----------------
  -- New results --
  -----------------

{-
  abstract

    ∃p⇨σᵗᵢⱼ≈xq : ∀ t → Acc _≤ℕ_ t → (p : EGPath G) → ∀ X → DiagonalAligned X → PathAligned X → ∃ λ (q : EGPath G) → σ^ (length p + t) X (source p) (destination p) ≈ᶜ croute (weight q) q refl
    ∃p⇨σᵗᵢⱼ≈xq zero    _          [ i ]                   X _ _ = [ i ] , {!!}
    ∃p⇨σᵗᵢⱼ≈xq zero    _          (_ ∷ _ ∣ _ ∣ _)          X _ _ = {!!}
    ∃p⇨σᵗᵢⱼ≈xq (suc t) _          [ i ]                   X _ _ = [ i ] , {!!}
    ∃p⇨σᵗᵢⱼ≈xq (suc t) (acc tAcc) (i ∷ p ∣ i∉p ∣ (v , e≈v)) X Xda Xpa with ∃p⇨σᵗᵢⱼ≈xq t {!!} p X Xda Xpa
    ...   | (q , σᵗ⁺¹ᵢₚ≈q) with i ∉? q
    ...     | yes i∉q = {!!} 
    ...     | no i∈q with ∃p⇨σᵗᵢⱼ≈xq {!!} {!tAcc ? ?!} (truncateAt i∈q) X Xda Xpa
    ...       | r , σᵗ⁺²X≈r = {!!}

      begin
        σ^ (suc (suc t)) X i (destination p)
      ≤⟨ σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕ᶜ-sel ⊕ᶜ-comm ⊕ᶜ-assoc (σ^ (suc t) X) i (destination p) (source p) ⟩
        Aᶜ i (source p) ▷ᶜ σ^ (suc t) X (source p) (destination p)
      ≈⟨ ▷ᶜ-pres-≈ᶜ (Aᶜ i (source p)) {!∃p⇨σᵗᵢⱼ≈xq ? ? ? ? ?!} ⟩
        Aᶜ i (source p) ▷ᶜ croute (weight p) p refl
      ≈⟨ ▷ᶜ-success refl refl i∉p ≡-refl e≈v ⟩
        croute (v ▷ weight p) (i ∷ p ∣ i∉p ∣ (v , e≈v)) refl
      ∎
--
-}

{-
 with σ^ (suc (suc t)) X i (destination p) | inspect (σ^ (suc (suc t)) X i) (destination p)
    ... | croute y q y≈w[q] | _               = q , crouteEq y≈w[q] ≈ₚ-refl
    ... | cnull             | [ σᵗ⁺²ᵢₚ≡cnull ] 
-}
