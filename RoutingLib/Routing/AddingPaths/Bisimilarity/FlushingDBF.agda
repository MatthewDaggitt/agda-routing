
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; s≤s)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Product using (∃₂; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst) renaming (refl to ≡-refl; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Graph using (Graph; _ᵉ∈ᵍ_)
open import RoutingLib.Data.Graph.EPath using (length; _∉?_; source; _∷_∣_; _≈ₚ_)
open import RoutingLib.Data.Graph.EPath.Properties using (≈ₚ-sym; ≈ₚ-trans; |p|<n; length-resp-≈ₚ; ∉-resp-≈ₚ; p≈q⇨p₀≡q₀)
open import RoutingLib.Data.Graph.EGPath using (to∉′′; to∉′; _∷_∣_∣_)
open import RoutingLib.Data.Graph.EGPath.Properties using (to[p]₀≡p₀)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties using (Selective)
open import RoutingLib.Data.Nat.Properties using (m+1≤n+1⇨m≤n)

module RoutingLib.Routing.AddingPaths.Bisimilarity.FlushingDBF
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (one : (RoutingAlgebra.Route ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  open RoutingAlgebra ra

  open import RoutingLib.Routing.AddingPaths.Inconsistent ra ⊕-sel one G using (_≈ⁱ_; ≈ⁱ-reflexive; ≈ⁱ-refl; ≈ⁱ-sym; ≈ⁱ-trans; inull; iroute; irouteEq; irp; Aⁱ; Iⁱ; _▷ⁱ_)
  open import RoutingLib.Routing.AddingPaths.Inconsistent.Properties ra ⊕-sel one G using (⊕ⁱ-sel)
  open import RoutingLib.Routing.AddingPaths.Consistent ra ⊕-sel one G using (CRoute; cnull; croute; Iᶜ)
  open import RoutingLib.Routing.AddingPaths.Bisimilarity ra ⊕-sel one G
  open import RoutingLib.Routing.AddingPaths.Bisimilarity.Reasoning ra ⊕-sel one G

  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord irp
  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties irp


  σ-extends-lemma : ∀ (X : RMatrix) {i j k : Fin n} {x p} → (Aⁱ i k ▷ⁱ X k j) ≈ⁱ iroute x p → ∃₂ λ v y → ∃₂ λ q i∉q → (x ≈ v ▷ y) × (p ≈ₚ i ∷ q ∣ i∉q) × (X k j ≈ⁱ iroute y q) × G i (source q) ≡ just v 
  σ-extends-lemma X {i} {j} {k} Aᵢₖ▷Xₖⱼ≈xp with G i k | X k j | inspect (G i) k
  ... | nothing          | _          | _ = contradiction Aᵢₖ▷Xₖⱼ≈xp λ()
  ... | just _           | inull      | _ = contradiction Aᵢₖ▷Xₖⱼ≈xp λ()
  ... | just v           | iroute y q | [ Gᵢₖ≡justv ] with k ≟ᶠ source q | i ∉? q
  ...   | no  _    | _       = contradiction Aᵢₖ▷Xₖⱼ≈xp λ()
  ...   | yes _    | no  _   = contradiction Aᵢₖ▷Xₖⱼ≈xp λ()
  ...   | yes k≡q₀ | yes i∉q with Aᵢₖ▷Xₖⱼ≈xp
  ...     | irouteEq v▷y≈x i∷q≈p = v , y , q , i∉q , sym v▷y≈x , ≈ₚ-sym i∷q≈p , ≈ⁱ-refl , subst (λ w → G i w ≡ just v) k≡q₀ Gᵢₖ≡justv



  flush : ∀ {X i j t x p} → σ^ t X i j ≈ⁱ iroute x p → length p < t → ∃ λ rᶜ → rᶜ ≃ iroute x p
  flush {X} {i} {j} {zero}  {x} {p} _ ()
  flush {X} {i} {j} {suc t} {x} {p} σᵗ⁺¹Xᵢⱼ≈xp |p|<t+1 with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕ⁱ-sel (σ^ t X) i j
  ... | inj₂ σᵗ⁺¹≈Iᵢⱼ      = Iᶜ i j , (cii-trans (Iᶜ≃Iⁱ i j ) (≈ⁱ-trans (≈ⁱ-sym σᵗ⁺¹≈Iᵢⱼ) σᵗ⁺¹Xᵢⱼ≈xp))
  ... | inj₁ (k , σᵗ⁺¹≈Aᵢₖ▷σᵗXₖⱼ) with σ-extends-lemma (σ^ t X) {j = j} (≈ⁱ-trans (≈ⁱ-sym σᵗ⁺¹≈Aᵢₖ▷σᵗXₖⱼ) σᵗ⁺¹Xᵢⱼ≈xp) 
  ...   | (v , y , q , i∉q , x≈v▷y , p≈i∷q , Xₖⱼ≈yq , Giq₀≡justv) with flush Xₖⱼ≈yq (m+1≤n+1⇨m≤n (subst (_< suc t) (length-resp-≈ₚ p≈i∷q) |p|<t+1))
  ...     | (cnull , ())
  ...     | (croute y' q' y'≈w[q']) , (routeEq y'≈y to[q']≈q) = croute (v ▷ y') (i ∷ q' ∣ to∉′′ (∉-resp-≈ₚ (≈ₚ-sym to[q']≈q) i∉q) ∣ (v , subst (λ w → G i w ≡ just v) (≡-trans (p≈q⇨p₀≡q₀ (≈ₚ-sym to[q']≈q)) (to[p]₀≡p₀ q')) Giq₀≡justv)) (▷-pres-≈ v y'≈w[q']) , routeEq (trans (▷-pres-≈ v y'≈y) (sym x≈v▷y)) (≈ₚ-trans (≡-refl _≈ₚ_.∷ to[q']≈q) (≈ₚ-sym p≈i∷q))



  i⇨c₂ : ∀ (X : RMatrix) i j → ∃ λ y → (y ≃ σ^ n X i j)
  i⇨c₂ X i j with σ^ n X i j | inspect (σ^ n X i) j
  ... | inull      | _          = cnull , nullEq
  ... | iroute x p | [ σⁿX≡xp ] with suc (length p) ≤? n
  ...   | yes |p|<n = flush (≈ⁱ-reflexive σⁿX≡xp) |p|<n
  ...   | no  |p|≮n = contradiction (|p|<n p) |p|≮n


  i⇨c : ∀ X → ∃ λ Y → Y ≃ₘ σ^ n X
  i⇨c X = (λ i j → proj₁ (i⇨c₂ X i j)) , (λ i j → proj₂ (i⇨c₂ X i j))
