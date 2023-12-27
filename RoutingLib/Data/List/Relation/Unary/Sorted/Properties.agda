open import Relation.Binary using (TotalOrder)
open import Data.Maybe using (nothing; just)
open import Data.Maybe.Relation.Binary.Connected hiding (refl)
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s; suc; ≤-pred) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties as ℕ using (≤⇒≯; suc-injective; module ≤-Reasoning; <-cmp)
open import Data.Fin as Fin using (Fin; Fin′; zero; suc; cast; pred; toℕ) renaming (_≤_ to _≤𝔽_; _<_ to _<𝔽_)
open import Data.Fin.Properties as Fin using (toℕ-cast; toℕ-injective; <⇒≢)
open import Data.Fin.Patterns
open import Data.Fin.Induction
open import Data.List as List hiding (tail)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; index)
open import Data.List.Membership.Propositional.Properties using (∈-lookup; ∈-∃++)
open import Data.List.Relation.Unary.AllPairs as AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Linked using ([]; [-]; _∷_; head′; _∷′_; tail)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒AllPairs)
open import Data.List.Properties
open import Data.List.Relation.Unary.All.Properties using (Any¬⇒¬All)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; uncurry′)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; cong) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; Decidable)

module RoutingLib.Data.List.Relation.Unary.Sorted.Properties
  {a ℓ₁ ℓ₂} (order : TotalOrder a ℓ₁ ℓ₂) where

open TotalOrder order renaming (Carrier to A)
open Eq using () renaming (setoid to S; trans to ≈-trans; sym to ≈-sym)

open import RoutingLib.Data.Fin.Properties as Fin
open import RoutingLib.Data.List.Relation.Unary.All.Properties as Allₚ
open import RoutingLib.Data.List.Relation.Unary.Linked.Properties using (lookup-Linked)
import Data.List.Relation.Binary.Permutation.Setoid.Properties S as Permₚ
open import Data.List.Relation.Unary.Sorted.TotalOrder order as Sorted hiding (tail)

open import Data.List.Relation.Binary.Permutation.Setoid S as Perm using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Equality.Setoid S
import Data.List.Relation.Binary.Pointwise as Pointwise

open import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties S
  using (xs↭ys⇒|xs|≡|ys|; permute; permute-lookup; permute-injective)
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties S using (length-mono-<; filter-⊂)

open import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.TotalOrder order

lookup-Sorted : ∀ {xs} → Sorted xs →
                ∀ {v} → Connected _≤_ (just v) (List.head xs) →
                ∀ i → v ≤ lookup xs i
lookup-Sorted xs↗ c i = lookup-Linked trans xs↗ c i

lookup-mono-≤ : ∀ {xs} → Sorted xs → ∀ {i j} → i ≤𝔽 j → lookup xs i ≤ lookup xs j
lookup-mono-≤ {x ∷ xs} xs↗ {zero}  {zero}  z≤n       = refl
lookup-mono-≤ {x ∷ xs} xs↗ {zero}  {suc j} z≤n       = lookup-Sorted xs↗ (just refl) (suc j)
lookup-mono-≤ {x ∷ xs} xs↗ {suc i} {suc j} (s≤s i≤j) = lookup-mono-≤ (tail xs↗) i≤j


private
  ↗↭↗⇒≤ : ∀ {xs ys} (xs↭ys : xs ↭ ys) → Sorted xs → Sorted ys →
          ∀ {i} → Acc Fin._<_ i →
          ∀ {j} → toℕ i ℕ.≤ toℕ j →
          (∀ k → i Fin.< k → toℕ k ℕ.≤ toℕ j → permute xs↭ys k Fin.< j) →
          ∀ {v} → lookup xs i ≤ v → lookup ys j ≤ v
  ↗↭↗⇒≤ {xs@(_ ∷ _)} {ys@(_ ∷ _)} xs↭ys xs↗ ys↗ {i} (acc rec) {j} i≤j ∀k {v} leq with j Fin.≤? permute xs↭ys i
  ...   | yes j≤πᵢ = begin
    lookup ys j                  ≤⟨  lookup-mono-≤ ys↗ j≤πᵢ ⟩
    lookup ys (permute xs↭ys i)  ≈˘⟨ permute-lookup xs↭ys i ⟩
    lookup xs i                  ≤⟨  leq ⟩
    v                            ∎
    where open PosetReasoning poset
  ...   | no  j≰πᵢ with i Fin.≟ zero
  ...     | yes ≡-refl = let (u , v , u<v , gu≡gv) = Fin.pigeonhole Fin.≤-refl g in
    contradiction gu≡gv (g-unique (<⇒≢ u<v))
    where
    j<∣xs∣ : toℕ j ℕ.< length xs
    j<∣xs∣ = P.subst (toℕ j ℕ.<_) (≡-sym (xs↭ys⇒|xs|≡|ys| xs↭ys)) (Fin.toℕ<n j)

    q : (x : Fin′ (suc j)) → permute xs↭ys (Fin.inject≤ x j<∣xs∣) Fin.< j
    q 0F      = ℕ.≰⇒> j≰πᵢ
    q (suc x) = ∀k _ (s≤s z≤n) (P.subst (_≤ℕ toℕ j) (≡-sym (Fin.toℕ-inject≤ (suc x) j<∣xs∣)) (Fin.toℕ<n x))
    
    g : Fin′ (suc j) → Fin′ j
    g x = lower (permute xs↭ys (Fin.inject≤ x j<∣xs∣)) (q x)

    g-unique : ∀ {x y} → x ≢ y → g x ≢ g y
    g-unique {x} {y} x≢y = x≢y
      ∘ Fin.inject≤-injective _ _ x y
      ∘ permute-injective xs↭ys
      ∘ lower-injective _ _ (q x) (q y)
    
  ...     | no  i≢0 = ↗↭↗⇒≤ xs↭ys xs↗ ys↗
    (rec {pred i} (ℕ.≤-reflexive (Fin.suc-pred i≢0)))
    (ℕ.≤-trans (Fin.≤-pred i) i≤j)
    eq
    (trans (lookup-mono-≤ xs↗ (Fin.≤-pred i)) leq)
    where

    eq : ∀ k → pred i <𝔽 k → toℕ k ≤ℕ toℕ j → permute xs↭ys k <𝔽 j
    eq k i∸1≤k k≤j with i Fin.≟ k
    ... | yes P.refl = ℕ.≰⇒> j≰πᵢ
    ... | no  i≢k    = ∀k k (ℕ.≤∧≢⇒< (P.subst (_≤ℕ toℕ k) (Fin.suc-pred i≢0) i∸1≤k) (i≢k ∘ toℕ-injective)) k≤j
    
↗↭↗⇒≋ : ∀ {xs ys} → Sorted xs → Sorted ys → xs ↭ ys → xs ≋ ys
↗↭↗⇒≋ {xs} {ys} xs↗ ys↗ xs↭ys = Pointwise.lookup⁻ (xs↭ys⇒|xs|≡|ys| xs↭ys) (λ {i} {j} i≡j → antisym
  (↗↭↗⇒≤ (↭-sym xs↭ys) ys↗ xs↗ (<-wellFounded j) (ℕ.≤-reflexive (≡-sym i≡j)) (λ k j<k k≤i → contradiction (ℕ.<-≤-trans j<k k≤i) (ℕ.<-irrefl (≡-sym i≡j))) refl)
  (↗↭↗⇒≤ xs↭ys         xs↗ ys↗ (<-wellFounded i) (ℕ.≤-reflexive i≡j)         (λ k i<k k≤j → contradiction (ℕ.<-≤-trans i<k k≤j) (ℕ.<-irrefl i≡j)) refl))
