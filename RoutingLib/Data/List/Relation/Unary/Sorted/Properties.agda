open import Relation.Binary using (DecTotalOrder)

module RoutingLib.Data.List.Relation.Unary.Sorted.Properties
  {a ℓ₁ ℓ₂} (order : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder order renaming (Carrier to A)
open Eq using () renaming (setoid to S; trans to ≈-trans; sym to ≈-sym)

open import Data.Nat using (ℕ; z≤n; s≤s; suc; ≤-pred) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤+≢⇒<; ≤⇒≯; <⇒≢; module ≤-Reasoning)
open import Data.Fin as Fin using (zero; suc; cast; toℕ) renaming (_≤_ to _≤𝔽_; _<_ to _<𝔽_)
open import Data.Fin.Properties using (toℕ-cast)
open import Data.List
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; index)
open import Data.List.Membership.Setoid.Properties using (∈-lookup)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Binary.Permutation.Setoid.Properties S as Permₚ
open import Data.List.Properties
open import Data.List.Relation.Unary.All.Properties using (Any¬⇒¬All)
open import Data.Product using (_,_; proj₁; proj₂; uncurry′)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; Decidable)

open import RoutingLib.Data.List using (insert; count)
open import RoutingLib.Data.List.Relation.Unary.All.Properties as Allₚ
open import RoutingLib.Data.List.Relation.Binary.Pointwise

open import RoutingLib.Data.List.Relation.Unary.Sorted totalOrder
open import Data.List.Membership.Setoid S using (_∈_)
open import Data.List.Relation.Binary.Permutation.Setoid S as Perm using (_↭_)
open import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties S
  using (xs↭ys⇒|xs|≡|ys|)
open import Data.List.Relation.Binary.Equality.Setoid S
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties S using (length-mono-<; filter-⊂)

open import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.DecTotalOrder order

private

  lemma : ∀ {x y xs} → All (x ≤_) xs → y ∈ xs → x ≤ y
  lemma [] ()
  lemma (px ∷ xs) (here  x≈z)  = proj₁ ≤-resp-≈ (≈-sym x≈z) px
  lemma (px ∷ xs) (there y∈xs) = lemma xs y∈xs
  
  lemma′ : ∀ {p} {P : Pred A p} (P? : Decidable P) {v xs} → v <ℕ count P? xs → Any P xs
  lemma′ P? {_} {x ∷ xs} 0< with P? x
  ... | yes px = here px 
  ... | no  _  = there (lemma′ P? 0<)
  
lookup-mono-≤ : ∀ {xs} → Sorted xs → ∀ {i j} → i ≤𝔽 j → lookup xs i ≤ lookup xs j
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {zero}  {zero}  z≤n = refl
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {zero}  {suc j} z≤n = lemma x≤xs (∈-lookup S xs j)
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {suc i} {zero}  ()
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {suc i} {suc j} (s≤s i≤j) = lookup-mono-≤ xs↗ i≤j

index-mono-< : ∀ {xs} → Sorted xs → ∀ {x y} (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) →
               x < y → index x∈xs <𝔽 index y∈xs
index-mono-< (x≤xs ∷ xs↗) (here x≈z)   (here y≈z) (x≤y , x≉y) = contradiction (≈-trans x≈z (≈-sym y≈z)) x≉y
index-mono-< (x≤xs ∷ xs↗) (here x≈z)   (there y∈xs) (x≤y , x≉y) = s≤s z≤n
index-mono-< (x≤xs ∷ xs↗) (there x∈xs) (here y≈z)    (x≤y , x≉y) = contradiction (antisym x≤y (proj₂ ≤-resp-≈ (≈-sym y≈z) (lemma x≤xs x∈xs))) x≉y
index-mono-< (x≤xs ∷ xs↗) (there x∈xs) (there y∈xs) x<y = s≤s (index-mono-< xs↗ x∈xs y∈xs x<y)

count-lookup2 : ∀ {xs} → Sorted xs → ∀ i → toℕ i <ℕ count (_≤? lookup xs i) xs
count-lookup2 {x ∷ xs} (x≤xs ∷ xs↗) zero    with x ≤? x
... | yes _   = s≤s z≤n
... | no  x≰x = contradiction refl x≰x
count-lookup2 {x ∷ xs} (x≤xs ∷ xs↗) (suc i) with x ≤? lookup xs i
... | yes _     = s≤s (count-lookup2 xs↗ i)
... | no  x≰xsᵢ = contradiction (All.lookup x≤xs (∈-lookup (≡-setoid A) xs i)) x≰xsᵢ

  
count-lookup : ∀ {xs} → Sorted xs → ∀ {v i} → toℕ i <ℕ count (_≤? v) xs → lookup xs i ≤ v
count-lookup {x ∷ xs} (x≤xs ∷ xs↗) {v} {i} i≤v with x ≤? v
... | no  x≰v = contradiction x≤xs (Any¬⇒¬All (Any.map (λ c≤v x≤c → x≰v (trans x≤c c≤v)) xsᵢ≤v))
  where
  xsᵢ≤v : Any (_≤ v) xs
  xsᵢ≤v = lemma′ (_≤? v) i≤v
... | yes x≤v with i
...   | zero  = x≤v
...   | suc _ = count-lookup xs↗ (≤-pred i≤v)

------------------------------------------------------------------------

insert↗⁺ : ∀ v {xs} → Sorted xs → Sorted (insert total v xs)
insert↗⁺ v {_}      []           = [] ∷ []
insert↗⁺ v {x ∷ xs} (x≤xs ∷ xs↗) with total v x
... | inj₁ v≤x = (v≤x ∷ All.map (trans v≤x) x≤xs) ∷ x≤xs ∷ xs↗
... | inj₂ x≤v = (Allₚ.insert⁺ total x≤v x≤xs) ∷ insert↗⁺ v xs↗

↗↭↗⇒≋ : ∀ {xs ys} → xs ↭ ys → Sorted xs → Sorted ys → xs ≋ ys
↗↭↗⇒≋ {xs} {ys} xs↭ys xs↗ ys↗ = lookup⁻ (xs↭ys⇒|xs|≡|ys| xs↭ys) lemma2
  where
  open ≤-Reasoning
  lemma1 : ∀ {xs ys} → xs ↭ ys → Sorted xs → Sorted ys → ∀ {i j} → toℕ i ≡ toℕ j → lookup xs i ≤ lookup ys j
  lemma1 {xs} {ys} xs↭ys xs↗ ys↗ {i} {j} i≡j = count-lookup xs↗ (begin-strict
    toℕ i                      ≡⟨ i≡j ⟩
    toℕ j                      <⟨ count-lookup2 ys↗ j ⟩
    count (_≤? lookup ys j) ys ≡⟨ xs↭ys⇒|xs|≡|ys| (Permₚ.filter⁺ (_≤? lookup ys j) ≤-respˡ-≈ (Perm.↭-sym xs↭ys)) ⟩
    count (_≤? lookup ys j) xs ∎)
  
  lemma2 : ∀ i → lookup xs i ≈ lookup ys (cast _ i)
  lemma2 i = antisym (lemma1 xs↭ys xs↗ ys↗ (≡-sym (toℕ-cast _ i))) (lemma1 (Perm.↭-sym xs↭ys) ys↗ xs↗ (toℕ-cast _ i))
