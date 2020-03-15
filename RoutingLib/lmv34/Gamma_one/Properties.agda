{-# OPTIONS --allow-unsolved-metas #-}
open import Algebra.Core
open import Algebra.Definitions
open import Data.Bool.Base using (true; false)
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_≤_; _≟_)
open import Data.Fin.Properties using (<-cmp; <-respˡ-≡; <-respʳ-≡; <-asym) renaming (≡-setoid to Fin-setoid)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; filter; tabulate; map; foldr)
open import Data.List.Properties
open import Data.List.Relation.Binary.Permutation.Propositional
  using ()
  renaming (_↭_ to _≡-↭_; refl to ≡-refl; prep to ≡-prep; trans to ≡-trans; swap to ≡-swap)
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermProperties
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Equality.Setoid as Equality
open import Data.List.Relation.Unary.All as All using (All) renaming ([] to []ₐ; _∷_ to _∷ₐ_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Sum using (inj₁; inj₂)
open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Nullary using (¬_; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Negation using (¬?; contradiction; contraposition)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Function using (_∘_)
open import Relation.Binary using (IsEquivalence; Setoid; DecSetoid; DecTotalOrder; Rel; Reflexive; _Respects_; _⇒_; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Iteration.Synchronous using (_^_; IsFixedPoint)
open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.Properties using (strictMerge-identityʳ; strictMerge-idempotent; strictMerge-cong)
import RoutingLib.Data.List.Relation.Unary.Sorted as Sorting
import RoutingLib.Data.List.Relation.Unary.Sorted.Properties as SortedProperties
import RoutingLib.Data.List.Sorting.InsertionSort as InsertionSort
import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as Perm

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.Data.Matrix using (SquareMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_zero.Properties as Gamma_zero_Properties
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Gamma_one.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open RoutingAlgebraProperties isRoutingAlgebra
open Routing algebra n renaming (I to M)
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n
open Gamma_zero_Properties algebra A using (IsFixedPoint-Γ₀)
open Gamma_one isRoutingAlgebra A
open Gamma_one_Algebra isRoutingAlgebra n

open Setoid (Fin-setoid n) using () renaming (refl to Fin-refl; sym to Fin-sym)
open DecSetoid FinRoute-decSetoid
  using (isEquivalence)
  renaming (_≈_ to _≈ᵣ_; refl to ≈ᵣ-refl; trans to ≈ᵣ-trans; sym to ≈ᵣ-sym)
open DecTotalOrder decTotalOrder using (≤-respˡ-≈; ≤-respʳ-≈; total; _≤_) renaming (antisym to ≤-antisym; refl to ≤-refl; trans to ≤-trans)
open InsertionSort decTotalOrder using (sort; sort↗; sort↭; sort-pres-↭)
open Sorting ≤₊-totalOrder using (Sorted)
open Equality FinRoute-setoid using (_≋_; ≋-refl; ≋-sym; ≋-trans)
open PermProperties FinRoute-setoid using (≋⇒↭)
open SortedProperties decTotalOrder using (↗↭↗⇒≋)

--------------------------------------------------------------------------------
-- Operation properties

-- MATTHEW : Neither of these are provable...
-- Only provable for the application operator _▷_
postulate
  f-cong : ∀ (f : Route → Route) {s s' : Route} → s ≈ s' → f s ≈ f s' -- need this to prove []-cong
  f-fix : ∀ (f : Route → Route) → f ∞# ≈ ∞# -- need this to prove ~-lemma

insert-min : ∀ {x xs} → All (x ≤_) xs → insert total x xs ≋ (x ∷ xs)
insert-min {x} {[]} x≤xs = ≋-refl
insert-min {x} {y ∷ xs} (x≤y¹ All.∷ x≤xs) with total x y
... | inj₁ x≤y² = ≋-refl
... | inj₂ y≤x  = (≈ᵣ-sym x=y) ∷ (≋-trans (insert-min x≤xs) (x=y ∷ ≋-refl))
  where
    x=y : x ≈ᵣ y
    x=y = ≤-antisym x≤y¹ y≤x
{-
All-≤-preserves-≈ᵣ : ∀ {x x' xs} → x ≈ᵣ x' → All (x ≤_) xs → All (x' ≤_) xs
All-≤-preserves-≈ᵣ x≈x' = All.map (≤-respˡ-≈ x≈x')

All-≤-trans : ∀ {xs x y} → x ≤ y → All (y ≤_) xs → All (x ≤_) xs
All-≤-trans x≤y = All.map (≤-trans x≤y)
-}
--------------------------------------------------------------------------------
-- Properties of `map₂`

map₂-map : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (xs : List (C × A)) (f : A → B) → map₂ f xs ≡ map (λ {(d , v) → (d , f v)}) xs
map₂-map [] f = refl
map₂-map ((d , v) ∷ xs) f = cong ((d , f v) ∷_) (map₂-map xs f)

map₂-tabulate : ∀ {a b c} {n} {A : Set a} {B : Set b} {C : Set c}
               (g : Fin n → C × A) (f : A → B) →
               map₂ f (tabulate g) ≡ tabulate ((λ {(d , v) → (d , f v)}) ∘ g)
map₂-tabulate g f = ≡ₗ-trans (map₂-map (tabulate g) f) (map-tabulate g (λ {(d , v) → (d , f v)}))
  where open import Relation.Binary.PropositionalEquality using () renaming (trans to ≡ₗ-trans)

--------------------------------------------------------------------------------
-- Properties of `_⊕_`

⊕-idempotent : Idempotent _≈_ _⊕_
⊕-idempotent v with ⊕-sel v v
... | inj₁ v⊕v=v = v⊕v=v
... | inj₂ v⊕v=v = v⊕v=v

--------------------------------------------------------------------------------
-- Properties of `_⊕₂_`

⊕₂-idem : Idempotent _≈ᵣ_ _⊕₂_
⊕₂-idem (d , v) = (refl , ⊕-idempotent v)

--------------------------------------------------------------------------------
-- Properties of _⊕ₛ_

⊕ₛ-cong : Congruent₂ _↭_  _⊕ₛ_
⊕ₛ-cong {A} {A'} {B} {B'} A↭A' B↭B' =
  ≋⇒↭ (strictMerge-cong isEquivalence ≤₂-isPreorder {!⊕₂-cong!}
    {!!}
    (↗↭↗⇒≋ (sort-pres-↭ B↭B') (sort↗ B) (sort↗ B')))
{-
  (↗↭↗⇒≋ (sort-pres-↭ A↭A') (sort↗ A) (sort↗ A'))
  (↗↭↗⇒≋ (sort-pres-↭ B↭B') (sort↗ B) (sort↗ B')))
-}

⊕ₛ-identityₗ : LeftIdentity _↭_ Ø _⊕ₛ_
⊕ₛ-identityₗ A = sort↭ A

⊕ₛ-identityᵣ : RightIdentity _↭_ Ø _⊕ₛ_
⊕ₛ-identityᵣ A = ↭-trans (↭-reflexive (strictMerge-identityʳ (sort A))) (sort↭ A)

⊕ₛ-identity : Identity _↭_ Ø _⊕ₛ_
⊕ₛ-identity = (⊕ₛ-identityₗ , ⊕ₛ-identityᵣ)

⊕ₛ-idempotent : Idempotent _↭_ _⊕ₛ_
⊕ₛ-idempotent xs = begin
  xs ⊕ₛ xs                        ≡⟨⟩
  mergeSorted (sort xs) (sort xs) ↭⟨ ≋⇒↭ (strictMerge-idempotent refl ⊕₂-idem (sort xs)) ⟩
  sort xs                         ↭⟨ sort↭ xs ⟩
  xs                              ∎
  where open PermutationReasoning

-- LEX: this is false. Counterexample: xs=[], ys=[x]. (x∷xs)⊕ₛys = [x]⊕ₛ[x] = [x] ¬↭ x∷x = x ∷ ([] ⊕ₛ [x])
⊕ₛ-cons : ∀ x xs ys → (x ∷ xs) ⊕ₛ ys ↭ x ∷ (xs ⊕ₛ ys)
⊕ₛ-cons x xs ys = begin
  (x ∷ xs) ⊕ₛ ys                        ≡⟨⟩
  mergeSorted (sort (x ∷ xs)) (sort ys) ↭⟨ {!!} ⟩
  mergeSorted (x ∷ (sort xs)) (sort ys) ↭⟨ {!!} ⟩
  x ∷ (mergeSorted (sort xs) (sort ys)) ≡⟨⟩
  x ∷ (xs ⊕ₛ ys)                        ∎
  where open PermutationReasoning
  
--------------------------------------------------------------------------------
-- Properties of IsValid

x=∞⇒fx=∞ : ∀ {v} {f : Route → Route} → v ≈ ∞# → f v ≈ ∞#
x=∞⇒fx=∞ {v} {f} v=∞ = ≈-trans (f-cong f v=∞) (f-fix f)

isValid-f : ∀ {d v} {f : Route → Route} → IsValid (d , f v) → IsValid (d , v)
isValid-f {d} {v} {f} = contraposition (x=∞⇒fx=∞ {v} {f})

isInvalid-f : ∀ {d v} {f : Route → Route} → IsInvalid (d , v) → IsInvalid (d , f v)
isInvalid-f {d} {v} {f} v=∞ = x=∞⇒fx=∞ {v} {f} v=∞

invalid-valid : ∀ {p} → IsInvalid p → ¬ (IsValid p)
invalid-valid p=∞ = λ p≠∞ → contradiction p=∞ p≠∞

valid-invalid : ∀ {p} → ¬ (IsValid p) → IsInvalid p
valid-invalid {d , v} ¬valid with v ≟ ∞#
... | yes v=∞ = v=∞
... | no v≠∞  = contradiction v≠∞ ¬valid

invalid-pair : ∀ d → IsInvalid (d , ∞#)
invalid-pair d = ≈-refl

--------------------------------------------------------------------------------
-- Properties of _⨁ₛ_

⨁ₛ-cong : ∀ {k} → {f g : Fin k → RoutingSet} →
          (∀ {i} → f i ↭ g i) → ⨁ₛ f ↭ ⨁ₛ g
⨁ₛ-cong {zero}  f=g = ↭-refl
⨁ₛ-cong {suc k} f=g = ⊕ₛ-cong f=g (⨁ₛ-cong {k} f=g)

--------------------------------------------------------------------------------
-- Properties of _⊕ᵥ_

⊕ᵥ-cong : Congruent₂ _≈ᵥ_ _⊕ᵥ_
⊕ᵥ-cong V=V' W=W' i = ⊕ₛ-cong (V=V' i) (W=W' i)

⊕ᵥ-identityₗ : LeftIdentity _≈ᵥ_ Øᵥ _⊕ᵥ_
⊕ᵥ-identityₗ A i = ⊕ₛ-identityₗ (A i)

⊕ᵥ-identityᵣ : RightIdentity _≈ᵥ_ Øᵥ _⊕ᵥ_
⊕ᵥ-identityᵣ A i = ⊕ₛ-identityᵣ (A i)

⊕̬ᵥ-identity : Identity _≈ᵥ_ Øᵥ _⊕ᵥ_
⊕̬ᵥ-identity = (⊕ᵥ-identityₗ , ⊕ᵥ-identityᵣ)

--------------------------------------------------------------------------------
-- Properties of †_

†-respects-≈ᵣ : IsValid Respects _≈ᵣ_
†-respects-≈ᵣ (_ , v₁=v₂) = _∘ ≈-trans (v₁=v₂)

†-cong : Congruent₁ _↭_ _†
†-cong A=A' = PermProperties.filter⁺ FinRoute-setoid IsValid? †-respects-≈ᵣ A=A'

†-identity : Ø † ↭ Ø
†-identity = ↭-refl

†-idempotent : IdempotentFun _↭_ _†
†-idempotent xs = ↭-reflexive (filter-idem IsValid? xs)

†-cons-valid : ∀ x xs → IsValid x → (x ∷ xs) † ≡ x ∷ (xs †)
†-cons-valid x xs valid = filter-accept IsValid? valid

†-cons-invalid : ∀ x xs → IsInvalid x → (x ∷ xs) † ≡ xs †
†-cons-invalid x xs invalid = filter-reject IsValid? (invalid-valid {x} invalid)

map-†-lemma : ∀ {xs f} → (map₂ f xs) † ↭ (map₂ f (xs †)) †
map-†-lemma {xs} {f} = ≋⇒↭ {!!}
{-
with IsValid? (d , v)
... | no invalid  = p
  where p : ((d , f v) ∷ (map₂ f xs)) † ↭ (map₂ f (xs †)) †
        p with IsValid? (d , f v)
        ... | no  _ = map-†-lemma {xs}
        ... | yes valid = contradiction (x=∞⇒fx=∞ {v} {f} (valid-invalid {d , v} invalid)) valid
... | yes _ with IsValid? (d , f v)
...   | no  _ = map-†-lemma {xs}
...   | yes _ = prep ≈ᵣ-refl (map-†-lemma {xs})
-}

†-⊕ₛ-distributive : ∀ {xs ys} → (xs †) ⊕ₛ (ys †) ↭ (xs ⊕ₛ ys) †
†-⊕ₛ-distributive {[]} {ys} = begin
  (Ø †) ⊕ₛ (ys †)  ≡⟨⟩
  Ø ⊕ₛ (ys †)      ↭⟨ ⊕ₛ-identityₗ (ys †) ⟩
  ys †             ↭⟨ †-cong (↭-sym (⊕ₛ-identityₗ ys)) ⟩
  (Ø ⊕ₛ ys) †      ∎
  where open PermutationReasoning
†-⊕ₛ-distributive {x ∷ xs} {[]} = begin
  ((x ∷ xs) †) ⊕ₛ (Ø †) ≡⟨⟩
  ((x ∷ xs) †) ⊕ₛ Ø     ↭⟨ ⊕ₛ-identityᵣ ((x ∷ xs) †) ⟩
  (x ∷ xs) †            ↭⟨ †-cong (↭-sym (⊕ₛ-identityᵣ (x ∷ xs))) ⟩
  ((x ∷ xs) ⊕ₛ Ø) †     ∎
  where open PermutationReasoning
†-⊕ₛ-distributive {x ∷ xs} {y ∷ ys} = {!!}

--------------------------------------------------------------------------------
-- Properties of _[_]

[]-cong : ∀ {f : Route → Route} {A A'} →
            A ↭ A' → f [ A ] ↭ f [ A' ]
[]-cong A=A' = †-cong (lemma A=A')
   where lemma : {A A' : RoutingSet} → {f : Route → Route} →
                 A ↭ A' → map₂ f A ↭ map₂ f A'
         lemma = PermProperties.map⁺ {!S!} {!!} {!!}

--------------------------------------------------------------------------------
-- Properties of _⟦_⟧

〚〛-cong : ∀ {V V'} → V ≈ᵥ V' → A 〚 V 〛 ≈ᵥ A 〚 V' 〛
〚〛-cong V=V' i = ⨁ₛ-cong (λ {q} → []-cong (V=V' q))

≈ₘ⇒≈ᵥ : ∀ {M M' : RoutingMatrix} → M ≈ₘ M' → ~ M ≈ᵥ ~ M'
(≈ₘ⇒≈ᵥ M=M') i = †-cong (Perm.tabulate⁺ FinRoute-setoid (λ {j} → (Fin-refl , M=M' i j)))

--------------------------------------------------------------------------------
-- Properties of Γ₁

Γ₁-cong : Congruent₁ _≈ᵥ_ Γ₁
Γ₁-cong V=V' = ⊕ᵥ-cong (〚〛-cong V=V') (≈ₘ⇒≈ᵥ ≈ₘ-refl)

Γ₁-iter-cong : ∀ k → Congruent₁ _≈ᵥ_ (Γ₁ ^ k)
Γ₁-iter-cong zero    V=V' = V=V'
Γ₁-iter-cong (suc k) V=V' = Γ₁-cong (Γ₁-iter-cong k V=V')

IsFixedPoint-Γ₁ : Pred RoutingVector (a ⊔ ℓ)
IsFixedPoint-Γ₁ V = Γ₁ V ≈ᵥ V

------------------------------------
-- Theorems 

-- Lemma A.2
private
  postulate
    lemma : ∀ (f g : Fin n → Route) → (tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d)) ↭ tabulate λ d → (d , f d ⊕ g d)

LemmaA₂ : ∀ (f g : Fin n → Route) →
          ((tabulate λ d → (d , f d)) †) ⊕ₛ ((tabulate λ d → (d , g d)) †) ↭
          (tabulate λ d → (d , f d ⊕ g d)) †
LemmaA₂ f g = begin
  ((tabulate λ d → (d , f d)) †) ⊕ₛ ((tabulate λ d → (d , g d)) †) ↭⟨ †-⊕ₛ-distributive {tabulate λ d → (d , f d)} {tabulate λ d → (d , g d)} ⟩
  ((tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d)))†      ↭⟨ †-cong {(tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d))} (lemma f g) ⟩
  (tabulate λ d → (d , f d ⊕ g d)) †                               ∎
  where open PermutationReasoning

tabulate-∞ : (tabulate (_, ∞#)) † ≡ []
tabulate-∞ = filter-none IsValid? (All.tabulate⁺ λ d → invalid-valid {d , ∞#} (invalid-pair d))

LemmaA₂-iter : ∀ {k} (f : Fin k → Fin n → Route) →
               ⨁ₛ (λ q → ((tabulate λ d → (d , f q d)) †)) ↭ (tabulate λ d → (d , (⨁ λ q → f q d))) †
LemmaA₂-iter {zero} f = ↭-reflexive (sym tabulate-∞)
LemmaA₂-iter {suc k} f = begin
  ⨁ₛ (λ q → ((tabulate λ d → (d , f q d)) †))                                                  ≡⟨⟩
  ((tabulate λ d → (d , f fzero d)) †) ⊕ₛ (⨁ₛ (λ q → ((tabulate λ d → (d , f (fsuc q) d)) †))) ↭⟨ ⊕ₛ-cong {(tabulate λ d → (d , f fzero d)) †} ↭-refl (LemmaA₂-iter (f ∘ fsuc)) ⟩
  ((tabulate λ d → (d , f fzero d)) †) ⊕ₛ ((tabulate λ d → (d , (⨁ (λ q → f (fsuc q) d)))) †)  ↭⟨ LemmaA₂ (f fzero) (λ d → ⨁ (λ q → f (fsuc q) d)) ⟩
  (tabulate λ d → (d , ((f fzero d) ⊕ (⨁ (λ q → f (fsuc q) d))))) †                            ≡⟨⟩
  (tabulate λ d → (d , (⨁ λ q → f q d))) † ∎
  where open PermutationReasoning

-- Lemma A.1
⊕-distributive : ∀ A B → ~(A ⊕ₘ B) ≈ᵥ (~ A) ⊕ᵥ (~ B)
⊕-distributive A B i = begin
  (~(A ⊕ₘ B)) i                                                        ≡⟨⟩
  (tabulate λ j → (j , (A i j) ⊕ (B i j))) †                           ↭⟨ ↭-sym (LemmaA₂ (λ j → A i j) (λ j → B i j)) ⟩
  ((tabulate (λ d → d , A i d)) †) ⊕ₛ ((tabulate (λ d → d , B i d)) †) ≡⟨⟩
  (~ A) i ⊕ₛ (~ B) i ∎
  where open PermutationReasoning

~-lemma : ∀ {i q Y} → map₂ (λ v → (A i q) ▷ v) ((~ Y) q) † ↭  (tabulate λ d → (d , (A i q) ▷ (Y q d))) †
~-lemma {i} {q} {Y} = begin
  map₂ (λ v → (A i q) ▷ v) ((~ Y) q) †                                   ≡⟨⟩
  (map₂ ((A i q) ▷_) ((tabulate (λ d → (d , Y q d))) †)) †               ↭⟨ ↭-sym (map-†-lemma {(tabulate (λ d → (d , Y q d)))}) ⟩
  (map₂ ((A i q) ▷_) (tabulate (λ d → (d , Y q d))))     †               ↭⟨ †-cong (↭-reflexive (map₂-tabulate ((λ d → (d , Y q d))) ((A i q) ▷_))) ⟩
  (tabulate ((λ {(d , v) → (d , (A i q) ▷ v)}) ∘ (λ d → (d , Y q d)))) † ≡⟨⟩
  (tabulate λ d → (d , (A i q) ▷ (Y q d))) † ∎
  where open PermutationReasoning

-- Lemma 3.1
Lemma-Γ₀=Γ₁ : ∀ {Y} → A 〚 ~ Y 〛 ≈ᵥ ~ (A 〔 Y 〕)
Lemma-Γ₀=Γ₁ {Y} i = begin
  (A 〚 ~ Y 〛) i                                        ≡⟨⟩
  ⨁ₛ (λ q → (A i q ▷_) [ (~ Y) q ])                     ≡⟨⟩
  ⨁ₛ (λ q → (λ s → (A i q) ▷ s) [ (~ Y) q ])            ≡⟨⟩  
  ⨁ₛ (λ q → (map₂ (λ v → (A i q) ▷ v) ((~ Y) q)) †)     ↭⟨ ⨁ₛ-cong (λ {q} → ~-lemma {i} {q} {Y}) ⟩
  ⨁ₛ (λ q → (tabulate λ d → (d , (A i q) ▷ (Y q d))) †) ↭⟨ LemmaA₂-iter (λ q d → (A i q) ▷ (Y q d)) ⟩
  (tabulate λ q → (q , ⨁ (λ k → (A i k) ▷ (Y k q)))) †  ≡⟨⟩
  (tabulate λ q → (q , (A 〔 Y 〕) i q)) †               ≡⟨⟩
  (~ (A 〔 Y 〕)) i ∎
  where open PermutationReasoning

-- Theorem 3
Γ₀=Γ₁ : {Y : RoutingMatrix} →
        Γ₁ (~ Y) ≈ᵥ ~ (Γ₀ Y)
Γ₀=Γ₁ {Y} = begin
  Γ₁ (~ Y)                ≡⟨⟩
  (A 〚 ~ Y 〛) ⊕ᵥ ~ M     ≈⟨ ⊕ᵥ-cong Lemma-Γ₀=Γ₁ (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
  (~ (A 〔 Y 〕)) ⊕ᵥ ~ M   ≈⟨ ≈ᵥ-sym (⊕-distributive (A 〔 Y 〕) M) ⟩
  ~ (A 〔 Y 〕 ⊕ₘ M)       ≡⟨⟩
  ~ (Γ₀ Y)                 ∎
  where open EqReasoning 𝕍ₛ

-- Theorem 4
Γ₀=Γ₁-iter : ∀ {k Y} → (Γ₁ ^ k) (~ Y) ≈ᵥ ~ ((Γ₀ ^ k) Y) 
Γ₀=Γ₁-iter {zero} {Y}  = ≈ᵥ-refl
Γ₀=Γ₁-iter {suc k} {Y} = begin
  (Γ₁ ^ suc k) (~ Y)   ≡⟨⟩
  Γ₁ ((Γ₁ ^ k) (~ Y))  ≈⟨ Γ₁-cong (Γ₀=Γ₁-iter {k}) ⟩
  Γ₁ (~ ((Γ₀ ^ k) Y))  ≈⟨ Γ₀=Γ₁ ⟩
  ~ (Γ₀ ((Γ₀ ^ k) Y))  ≡⟨⟩
  ~ (Γ₀ ^ suc k) Y     ∎
  where open EqReasoning 𝕍ₛ

-- Theorem 2
FixedPoint-Γ₀-Γ₁ : ∀ {X} → IsFixedPoint-Γ₀ X → IsFixedPoint-Γ₁ (~ X)
FixedPoint-Γ₀-Γ₁ {X} FP-Γ₀ = begin
  Γ₁ (~ X)           ≈⟨ Γ₀=Γ₁ ⟩
  ~ (Γ₀ X)           ≈⟨ ≈ₘ⇒≈ᵥ FP-Γ₀ ⟩
  ~ X                ∎
  where open EqReasoning 𝕍ₛ
