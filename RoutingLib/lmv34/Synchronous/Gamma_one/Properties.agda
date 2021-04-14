open import Algebra.Core
open import Algebra.Definitions
open import Data.Bool.Base using (true; false)
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_≤_; _≟_)
open import Data.Fin.Properties as Fin using (≤-trans; <-trans; <-cmp; <-respˡ-≡; <-respʳ-≡; <-asym; <⇒≢; ≤∧≢⇒<) renaming (≡-setoid to Fin-setoid)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (<⇒≤)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; filter; tabulate; map; foldr; head)
open import Data.List.Properties
import Data.List.Sort as Sort
open import Data.Maybe.Base using (just; nothing)
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermProperties
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Equality.Setoid as Equality
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.Sorted.TotalOrder as Sorting
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as SortedProperties
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (id)
open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Nullary using (¬_; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Negation using (¬?; contradiction; contraposition)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Function using (_∘_)
open import Relation.Binary as B 
open import Relation.Binary.Construct.NonStrictToStrict using (<-≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym) renaming (trans to ≡-trans)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Iteration.Synchronous using (_^_; IsFixedPoint)
open import RoutingLib.Data.List using () renaming (partialMerge to partialMerge')
open import RoutingLib.Data.List.Properties
  using (partialMerge-identityʳ; partialMerge-∷ˡ-min; partialMerge-∷ʳ-min; partialMerge-∷-eq; partialMerge-idempotent; partialMerge-cong)
open import RoutingLib.Data.Maybe.Relation.Binary.Connected.Left as Connectedˡ using (Connectedˡ; just; nothing)
open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix₁)

import RoutingLib.lmv34.Synchronous.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Synchronous.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Synchronous.Gamma_zero.Properties as Gamma_zero_Properties
import RoutingLib.lmv34.Synchronous.Gamma_one as Gamma_one
import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Synchronous.Gamma_one.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix₁ algebra n)
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

open Sort ≤ₐₜ-decTotalOrder
open module Sorted = Sorting ≤ₐₜ-totalOrder using (Sorted)
open Equality 𝔸ₛ using (_≋_; ≋-refl; ≋-sym; ≋-trans; ≋-reflexive)
open PermProperties 𝔸ₛ using (≋⇒↭)
import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as Perm
open import Data.List.Relation.Unary.Linked
  using () renaming (head′ to head↗; tail to tail↗; _∷′_ to _∷↗_)
open import RoutingLib.Data.List.Relation.Unary.Sorted.Properties ≤ₐₜ-totalOrder
  using (↗↭↗⇒≋)
open import RoutingLib.Data.List.Sort.Properties sortingAlgorithm

--------------------------------------------------------------------------------
-- Operation properties

-- MATTHEW : Neither of these are provable...
-- Only provable for the application operator _▷_
-- LEX: iirc, these were put here because the adjacency matrix A was a matrix
-- of Steps, but the decomposed matrices Exp, Prot, Imp (Gamma_2) had to be
-- matrices of the more general type "Route → Route". Tim mentioned this at some
-- point. Probably worth checking out if this is still necessary, or whether we
-- could have Exp, Prot, Imp be of type AdjacencyMatrix as well.
postulate
  f-cong : ∀ (f : Route → Route) {s s' : Route} → s ≈ s' → f s ≈ f s' -- need this to prove []-cong
  f-fix : ∀ (f : Route → Route) → f ∞# ≈ ∞# -- need this to prove ~-lemma

--------------------------------------------------------------------------------
-- Properties of `map₂`

map₂-map : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (xs : List (C × A)) (f : A → B) →
           map₂ f xs ≡ map (λ {(d , v) → (d , f v)}) xs
map₂-map [] f = refl
map₂-map ((d , v) ∷ xs) f = cong ((d , f v) ∷_) (map₂-map xs f)

map₂-tabulate : ∀ {a b c} {n} {A : Set a} {B : Set b} {C : Set c}
               (g : Fin n → C × A) (f : A → B) →
               map₂ f (tabulate g) ≡ tabulate ((λ {(d , v) → (d , f v)}) ∘ g)
map₂-tabulate g f = ≡-trans (map₂-map (tabulate g) f) (map-tabulate g (λ {(d , v) → (d , f v)}))

--------------------------------------------------------------------------------
-- Properties of _⊕ₐ_

⊕ₐ-cong : Congruent₂ _≈ₐ_ _⊕ₐ_
⊕ₐ-cong (refl , x≈y) (refl , w≈z) = refl , ⊕-cong x≈y w≈z

⊕ₐ-idem : Idempotent _≈ₐ_ _⊕ₐ_
⊕ₐ-idem (d , v) = refl , ⊕-idem v

⊕ₐ-invalid : ∀ x y → IsInvalid x → IsInvalid y → IsInvalid (x ⊕ₐ y)
⊕ₐ-invalid x y x=∞ y=∞ = ≈-trans (⊕-cong x=∞ y=∞) (⊕-idem ∞#)

⊕ₐ-valid : ∀ x y → IsValid x → IsValid y → IsValid (x ⊕ₐ y)
⊕ₐ-valid (_ , v₁) (_ , vₐ) v₁≠∞ vₐ≠∞ v₁⊕vₐ=∞ with ⊕-sel v₁ vₐ
... | inj₁ v₁⊕vₐ=v₁ = contradiction (≈-trans (≈-sym v₁⊕vₐ=v₁) v₁⊕vₐ=∞) v₁≠∞
... | inj₂ v₁⊕vₐ=vₐ = contradiction (≈-trans (≈-sym v₁⊕vₐ=vₐ) v₁⊕vₐ=∞) vₐ≠∞

--------------------------------------------------------------------------------
-- Properties of mergeSorted

mergeSorted-cong : ∀ {xs xs' ys ys'} → xs ≋ xs' → ys ≋ ys' → mergeSorted xs ys ≋ mergeSorted xs' ys' 
mergeSorted-cong = partialMerge-cong ≈ₐ-isEquivalence <ₐₜ-resp-≈ₐ ⊕ₐ-cong

mergeSorted-idem : Idempotent _↭_ mergeSorted
mergeSorted-idem xs = ≋⇒↭ (partialMerge-idempotent ≈ₐ-refl <ₐₜ-irrefl ⊕ₐ-idem xs)

mergeSorted-identityʳ : RightIdentity _↭_ [] mergeSorted
mergeSorted-identityʳ xs = ↭-reflexive (partialMerge-identityʳ xs)

--------------------------------------------------------------------------------
-- Properties of _⊕ₛ_

⊕ₛ-cong : Congruent₂ _↭_  _⊕ₛ_
⊕ₛ-cong A↭A' B↭B' = ≋⇒↭ (mergeSorted-cong (↭⇒sort-≋ A↭A') (↭⇒sort-≋ B↭B'))

⊕ₛ-identityₗ : LeftIdentity _↭_ Ø _⊕ₛ_
⊕ₛ-identityₗ A rewrite sort-[] = sort-↭ₛ A

⊕ₛ-identityᵣ : RightIdentity _↭_ Ø _⊕ₛ_
⊕ₛ-identityᵣ A rewrite sort-[] = ↭-trans (mergeSorted-identityʳ (sort A)) (sort-↭ₛ A)

⊕ₛ-identity : Identity _↭_ Ø _⊕ₛ_
⊕ₛ-identity = ⊕ₛ-identityₗ , ⊕ₛ-identityᵣ

⊕ₛ-idem : Idempotent _↭_ _⊕ₛ_
⊕ₛ-idem xs = begin
  mergeSorted (sort xs) (sort xs) ↭⟨ mergeSorted-idem (sort xs) ⟩
  sort xs                         ↭⟨ sort-↭ₛ xs ⟩
  xs                              ∎
  where open PermutationReasoning

--------------------------------------------------------------------------------
-- Properties of IsValid / IsInvalid

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

invalid-cong : ∀ {x y} → x ≈ₐ y → IsInvalid x → IsInvalid y
invalid-cong (x₁=y₁ , x₂=y₂) x-invalid = ≈-trans (≈-sym x₂=y₂) x-invalid

valid-cong : ∀ {x y} → x ≈ₐ y → IsValid x → IsValid y
valid-cong x=y = contraposition (invalid-cong (≈ₐ-sym x=y))

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

⊕ᵥ-identity : Identity _≈ᵥ_ Øᵥ _⊕ᵥ_
⊕ᵥ-identity = ⊕ᵥ-identityₗ , ⊕ᵥ-identityᵣ

⊕ᵥ-idem : Idempotent _≈ᵥ_ _⊕ᵥ_
⊕ᵥ-idem V i = ⊕ₛ-idem (V i)

--------------------------------------------------------------------------------
-- Properties of †_

†-respects-≈ₐ : IsValid Respects _≈ₐ_
†-respects-≈ₐ (_ , v₁=v₂) = _∘ ≈-trans (v₁=v₂)

†-cong : Congruent₁ _↭_ _†
†-cong A=A' = PermProperties.filter⁺ 𝔸ₛ IsValid? †-respects-≈ₐ A=A'

†-identity : Ø † ↭ Ø
†-identity = ↭-refl

†-idem : IdempotentFun _↭_ _†
†-idem xs = ↭-reflexive (filter-idem IsValid? xs)

†-cons-valid : ∀ x xs → IsValid x → (x ∷ xs) † ≡ x ∷ (xs †)
†-cons-valid x xs valid = filter-accept IsValid? valid

†-cons-invalid : ∀ x xs → IsInvalid x → (x ∷ xs) † ≡ xs †
†-cons-invalid x xs invalid = filter-reject IsValid? (invalid-valid {x} invalid)

map-†-lemma : ∀ f xs → (map₂ f xs) † ≡ (map₂ f (xs †)) †
map-†-lemma f []             = refl
map-†-lemma f ((d , v) ∷ xs) with IsInvalid? (d , v)
... | yes invalid = ≡-trans (†-cons-invalid (d , f v) (map₂ f xs) (isInvalid-f {d} {v} {f} invalid)) (map-†-lemma f xs)
... | no  _       with IsInvalid? (d , f v)
...   | no  _ = cong ((d , f v) ∷_) (map-†-lemma f xs)
...   | yes _ = map-†-lemma f xs

con-<-transʳ : ∀ {v x xs} → v <ₐₜ x → Connectedˡ _≤ₐₜ_ x (head xs) → Connectedˡ _<ₐₜ_ v (head xs)
con-<-transʳ {xs = []}     v<x nothing    = nothing
con-<-transʳ {xs = y ∷ xs} v<x (just x≤y) = just (<ₐₜ-≤ₐₜ-trans v<x x≤y)

con-<-† : ∀ {v xs} → Sorted xs → Connectedˡ _<ₐₜ_ v (head xs) → Connectedˡ _<ₐₜ_ v (head (xs †))
con-<-† {v} {[]}     _   _          = nothing
con-<-† {v} {x ∷ xs} xs↗ (just v<x) with IsInvalid? x
... | yes _ = con-<-† (tail↗ xs↗) (con-<-transʳ v<x (head↗ xs↗))
... | no  _ = just v<x

†-distrib-sort : ∀ xs → sort (xs †) ≋ (sort xs) †
†-distrib-sort xs = sort-filter-≋ IsValid? valid-cong xs

†-distrib-mergeSorted-⊕ : ∀ {x y xs ys} → x ≈ₐ y →
                          mergeSorted (xs †) (ys †) ↭ (mergeSorted xs ys) † →
                          mergeSorted ((x ∷ xs) †) ((y ∷ ys) †) ↭ (x ⊕ₐ y ∷ mergeSorted xs ys) †
†-distrib-mergeSorted-⊕ {x} {y} {xs} {ys} x≈y rec with IsInvalid? x | IsInvalid? y
... | yes xⁱ | no  yᵛ = contradiction (invalid-cong x≈y xⁱ) yᵛ
... | no  xᵛ | yes yⁱ = contradiction yⁱ (valid-cong x≈y xᵛ)
... | yes xⁱ | yes yⁱ = begin
  mergeSorted (xs †) (ys †)      ↭⟨ rec ⟩
  (mergeSorted xs ys) †          ≡˘⟨ †-cons-invalid (x ⊕ₐ y) (mergeSorted xs ys) (⊕ₐ-invalid x y xⁱ yⁱ) ⟩
  (x ⊕ₐ y ∷ mergeSorted xs ys) † ∎
  where open PermutationReasoning
... | no  xᵛ   | no  yᵛ   = begin
  mergeSorted (x ∷ (xs †)) (y ∷ (ys †)) ≡⟨  partialMerge-∷-eq ≈ₐ-sym <ₐₜ-irrefl {xs = xs †} {ys = ys †} x≈y ⟩
  x ⊕ₐ y ∷ mergeSorted (xs †) (ys †)    ↭⟨  ↭-prep (x ⊕ₐ y) rec ⟩
  x ⊕ₐ y ∷ (mergeSorted xs ys) †        ≡˘⟨ †-cons-valid (x ⊕ₐ y) (mergeSorted xs ys) (⊕ₐ-valid x y xᵛ yᵛ) ⟩
  (x ⊕ₐ y ∷ mergeSorted xs ys) †        ∎
  where open PermutationReasoning
  
†-distrib-mergeSorted : ∀ {xs ys} → Sorted xs → Sorted ys →
                        mergeSorted (xs †) (ys †) ↭ (mergeSorted xs ys) †
†-distrib-mergeSorted {[]}     {ys}     _   _   = ↭-refl
†-distrib-mergeSorted {x ∷ xs} {[]}     _   _   = mergeSorted-identityʳ ((x ∷ xs) †)
†-distrib-mergeSorted {x ∷ xs} {y ∷ ys} xs↗ ys↗ with <ₐₜ-cmp x y
  | †-distrib-mergeSorted xs↗         (tail↗ ys↗)
  | †-distrib-mergeSorted (tail↗ xs↗) ys↗
  | †-distrib-mergeSorted (tail↗ xs↗) (tail↗ ys↗)
... | tri≈ _ x≈y _ | _ | _ | rec₃ = †-distrib-mergeSorted-⊕ x≈y rec₃
... | tri< x<y _ _ | _ | rec₂ | _ = prf
  where prf : mergeSorted ((x ∷ xs) †) ((y ∷ ys) †) ↭ (x ∷ (mergeSorted xs (y ∷ ys))) †
        prf with IsInvalid? x
        ... | yes x-invalid = rec₂
        ... | no  x-valid   = ↭-trans (↭-reflexive (partialMerge-∷ˡ-min <ₐₜ-asym All-<-ys)) (prep ≈ₐ-refl rec₂)
          where All-<-ys : Connectedˡ _<ₐₜ_ x (head ((y ∷ ys) †))
                All-<-ys = con-<-† ys↗ (just x<y)
... | tri> _ _ y<x | rec₁ | _ | _ = prf
  where prf : mergeSorted ((x ∷ xs) †) ((y ∷ ys) †) ↭ (y ∷ (mergeSorted (x ∷ xs) ys)) †
        prf with IsInvalid? y
        ... | yes y-invalid = rec₁
        ... | no  y-valid   = ↭-trans (↭-reflexive (partialMerge-∷ʳ-min <ₐₜ-asym All-<-xs)) (prep ≈ₐ-refl rec₁)
          where All-<-xs : Connectedˡ _<ₐₜ_ y (head ((x ∷ xs) †))
                All-<-xs = con-<-† xs↗ (just y<x)

†-⊕ₛ-distributive : ∀ {xs ys} → (xs †) ⊕ₛ (ys †) ↭ (xs ⊕ₛ ys) †
†-⊕ₛ-distributive {xs} {ys} = begin
  (xs †) ⊕ₛ (ys †)                        ≡⟨⟩
  mergeSorted (sort (xs †)) (sort (ys †)) ≋⟨ mergeSorted-cong (†-distrib-sort xs) (†-distrib-sort ys) ⟩
  mergeSorted ((sort xs) †) ((sort ys) †) ↭⟨ †-distrib-mergeSorted (sort-↗ xs) (sort-↗ ys) ⟩
  (xs ⊕ₛ ys) †                            ∎
  where open PermutationReasoning

--------------------------------------------------------------------------------
-- Properties of _[_]

[]-cong : ∀ {f : Route → Route} {A A'} →
            A ↭ A' → f [ A ] ↭ f [ A' ]
[]-cong {f} A=A' = †-cong (lemma A=A')
   where f-cong₂ : ∀ {d d' : Fin n} {v v' : Route} → 
                   (d , v) ≈ₐ (d' , v') → (d , f v) ≈ₐ (d' , f v')
         f-cong₂ (d=d' , v=v') = d=d' , f-cong f v=v'
         lemma : {A A' : RoutingSet} →
                 A ↭ A' → map₂ f A ↭ map₂ f A'
         lemma = PermProperties.map⁺ 𝔸ₛ 𝔸ₛ f-cong₂

--------------------------------------------------------------------------------
-- Properties of _⟦_⟧

〚〛-cong : ∀ {A} {V V'} → V ≈ᵥ V' → A 〚 V 〛 ≈ᵥ A 〚 V' 〛
〚〛-cong V=V' i = ⨁ₛ-cong (λ {q} → []-cong (V=V' q))

≈ₘ⇒≈ᵥ : ∀ {M M' : RoutingMatrix} → M ≈ₘ M' → ~ M ≈ᵥ ~ M'
(≈ₘ⇒≈ᵥ M=M') i = †-cong (Perm.tabulate⁺ 𝔸ₛ (λ {j} → (Fin-refl , M=M' i j)))

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
⊕ᵥ-distributive : ∀ A B → ~(A ⊕ₘ B) ≈ᵥ (~ A) ⊕ᵥ (~ B)
⊕ᵥ-distributive A B i = begin
  (~(A ⊕ₘ B)) i                                                        ≡⟨⟩
  (tabulate λ j → (j , (A i j) ⊕ (B i j))) †                           ↭⟨ ↭-sym (LemmaA₂ (λ j → A i j) (λ j → B i j)) ⟩
  ((tabulate (λ d → d , A i d)) †) ⊕ₛ ((tabulate (λ d → d , B i d)) †) ≡⟨⟩
  (~ A) i ⊕ₛ (~ B) i ∎
  where open PermutationReasoning

~-lemma : ∀ {i q Y} → {A : AdjacencyMatrix} →
          map₂ (λ v → (A i q) ▷ v) ((~ Y) q) † ↭  (tabulate λ d → (d , (A i q) ▷ (Y q d))) †
~-lemma {i} {q} {Y} {A} = begin
  map₂ (λ v → (A i q) ▷ v) ((~ Y) q) †                                   ≡⟨⟩
  (map₂ ((A i q) ▷_) ((tabulate (λ d → (d , Y q d))) †)) †               ≡⟨ sym (map-†-lemma ((A i q) ▷_) (tabulate (λ d → (d , Y q d)))) ⟩
  (map₂ ((A i q) ▷_) (tabulate (λ d → (d , Y q d))))     †               ↭⟨ †-cong (↭-reflexive (map₂-tabulate ((λ d → (d , Y q d))) ((A i q) ▷_))) ⟩
  (tabulate ((λ {(d , v) → (d , (A i q) ▷ v)}) ∘ (λ d → (d , Y q d)))) † ≡⟨⟩
  (tabulate λ d → (d , (A i q) ▷ (Y q d))) † ∎
  where open PermutationReasoning

-- Lemma 3.1
Lemma-Γ₀=Γ₁ : ∀ {A Y} → A 〚 ~ Y 〛 ≈ᵥ ~ (A 〔 Y 〕)
Lemma-Γ₀=Γ₁ {A} {Y} i = begin
  (A 〚 ~ Y 〛) i                                        ≡⟨⟩
  ⨁ₛ (λ q → (A i q ▷_) [ (~ Y) q ])                     ≡⟨⟩
  ⨁ₛ (λ q → (λ s → (A i q) ▷ s) [ (~ Y) q ])            ≡⟨⟩  
  ⨁ₛ (λ q → (map₂ (λ v → (A i q) ▷ v) ((~ Y) q)) †)     ↭⟨ ⨁ₛ-cong (λ {q} → ~-lemma {i} {q} {Y} {A}) ⟩
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
  (~ (A 〔 Y 〕)) ⊕ᵥ ~ M   ≈⟨ ≈ᵥ-sym (⊕ᵥ-distributive (A 〔 Y 〕) M) ⟩
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
