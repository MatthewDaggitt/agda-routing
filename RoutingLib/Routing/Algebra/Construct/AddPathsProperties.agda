
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Construct.AddPathsProperties
  {a b ℓ} (A : RawRoutingAlgebra a b ℓ)
  (A-IsRoutingAlgebra  : IsRoutingAlgebra A) where

open import Algebra.Construct.NaturalChoice.Min
open import Algebra.FunctionProperties
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Maybe.Relation.Unary.All using (just)
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent as Pointwise using (Pointwise)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Lift; lift; _⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqReasoning
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq)
  using (∙≈∙; [_]; [≈]-injective; ≈∙-refl; ≈∙-sym; ≈∙-trans)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Construct.Add.Point renaming (∙ to invalid; [_] to valid)

import RoutingLib.Routing.Algebra.Properties.PathAlgebra as PathAlgebraProperties
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties
open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using (⊕∙-comm)
open import RoutingLib.Algebra.Construct.Lexicographic as Lex
  using (Lex; Lex₂)
open import RoutingLib.Algebra.Construct.Lexicographic.Magma as OpLexProperties′
open import RoutingLib.Data.Path.Uncertified.Choice
open import RoutingLib.Data.Path.Uncertified.Properties
open import RoutingLib.Data.Path.UncertifiedI using (Pathᵛ; Path; _∉ᵥₚ_; _∈ᵥₚ_; _⇿ᵥ_; _∈ₚ_; _∉ₚ_;_⇿_;_∷_ ) 
open import RoutingLib.Relation.Nullary.Negation using (contradiction₂)

open import RoutingLib.Routing.Algebra.Construct.AddPaths A
  hiding (⊕⁺-comm; ⊕⁺-identityʳ)


open RawRoutingAlgebra A
open IsRoutingAlgebra A-IsRoutingAlgebra

no-∞-sum : ∀ {x y} → x ≉ ∞# → y ≉ ∞# → (x ⊕ y) ≉ ∞#
no-∞-sum {x} {y} x≉∞ y≉∞  with ⊕-sel x y
... | inj₁ x⊕y≈x = λ x⊕y≈∞ → contradiction (≈-trans (≈-sym x⊕y≈x) x⊕y≈∞) x≉∞
... | inj₂ x⊕y≈y = λ x⊕y≈∞ → contradiction (≈-trans (≈-sym x⊕y≈y) x⊕y≈∞) y≉∞



Aᵖ : RawRoutingAlgebra a b (a ⊔ ℓ)
Aᵖ = AddPaths

open RawRoutingAlgebra Aᵖ using () renaming
     (≤₊-respˡ-≈          to  ≤₊⁺-respˡ-≈⁺;
      ≤₊-respʳ-≈          to  ≤₊⁺-respʳ-≈⁺;
      _≤₊_               to _≤₊⁺_;
      S             to S⁺
     )

Aᵖ-IsRoutingAlgebra : IsRoutingAlgebra Aᵖ
Aᵖ-IsRoutingAlgebra = isRoutingAlgebra A-IsRoutingAlgebra   
     where open IsRoutingAlgebra A-IsRoutingAlgebra

open IsRoutingAlgebra Aᵖ-IsRoutingAlgebra  renaming
  ( ⊕-sel        to ⊕⁺-sel
  ; ⊕-comm       to ⊕⁺-comm
  ; ⊕-assoc      to ⊕⁺-assoc
  ; ⊕-zeroʳ      to ⊕⁺-zeroʳ
  ; ⊕-identityʳ  to ⊕⁺-identityʳ
  ; ▷-fixedPoint to ▷⁺-fixedPoint  
  )

open RoutingAlgebraProperties Aᵖ-IsRoutingAlgebra
  using () renaming (≤₊-poset to ≤₊⁺-poset)

open RoutingAlgebraProperties A-IsRoutingAlgebra
  using (⊕-idem)

Aᵖ-IsPathAlgebra : IsPathAlgebra Aᵖ
Aᵖ-IsPathAlgebra = isPathAlgebra

open IsPathAlgebra Aᵖ-IsPathAlgebra
open PathDistributivity Aᵖ-IsPathAlgebra
open PathAlgebraProperties Aᵖ-IsRoutingAlgebra Aᵖ-IsPathAlgebra

private
  lemma₁ : ∀ {n} {i j : Fin n} {f : Step i j} {x} {y} → f ▷ x ≉ ∞# → f ▷ y ≉ ∞# → f ▷ x ⊕ y ≉ ∞#
  lemma₁ = {!!}

  lemma₂ : ∀ {n} {i j : Fin n} {f : Step i j} {x} {y} → f ▷ x ≈ ∞# → f ▷ y ≈ ∞# → f ▷ x ⊕ y ≈ ∞#
  lemma₂ = {!!}
  
open POR ≤₊⁺-poset

pres-distrib : ∀ {k ⊤ ⊥} p → Level_DistributiveIn[_,_]Alt A k ⊥ ⊤ →
               IsLevel_PathDistributiveIn[_,_]Alt k (valid (⊥ , p)) (valid (⊤ , p))
pres-distrib {zero}  p (lift ⊥≈⊤) = Level.lift [ ⊥≈⊤ , refl ]
pres-distrib {suc k} p _ f {invalid} {invalid} _ _ _ _ _ _ _ _ = isLevelPDistrib-equal k ∙≈∙
pres-distrib {suc k} p _ f {invalid} {valid y} _ _ _ _ _ _ _ _ = isLevelPDistrib-equal k ≈⁺-refl
pres-distrib {suc k} p _ f {valid x} {invalid} _ _ _ _ _ _ _ _ = isLevelPDistrib-equal k (≈⁺-sym (⊕⁺-identityʳ _))
pres-distrib {suc k} p distrib {n} {i} {j} f {valid (x , r)} {valid (y , s)} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s (just ij⇿r) (just ij⇿s)
  with ∞# ≟ f ▷ x  | ∞# ≟ f ▷ y  
... | yes ∞≈f▷x | yes ∞≈f▷y = isLevelPDistrib-equal k (begin-equality
  f ▷⁺ (valid (x , r)  ⊕⁺ valid (y , s))       ≈⟨ ▷⁺-reject-≈∞ (lemma₂ (≈-sym ∞≈f▷x) (≈-sym ∞≈f▷y)) ⟩
  ∞#⁺                                          ≡⟨⟩
  ∞#⁺                  ⊕⁺ ∞#⁺                  ≈⟨ ≈⁺-sym (⊕⁺-cong (▷⁺-reject-≈∞ (≈-sym ∞≈f▷x)) (▷⁺-reject-≈∞ (≈-sym ∞≈f▷y))) ⟩
  (f ▷⁺ valid (x , r)) ⊕⁺ (f ▷⁺ valid (y , s)) ∎)
... | yes _     | no      _ = {!IsLevel k PathDistributiveIn[ f ▷ (x ⊕ y) , f ▷ y ]Alt!}
... | no  _     | yes _     = {!!}
... | no  ∞≉f▷x | no  ∞≉f▷y with lemma₁ (∞≉f▷x ∘ ≈-sym) (∞≉f▷y ∘ ≈-sym)
...   | f▷x⊕y≉∞ with distrib f (≤₊⁺⇒≤⁺ ⊥≤x) (≤₊⁺⇒≤⁺ x≤⊤) (≤₊⁺⇒≤⁺ ⊥≤y) (≤₊⁺⇒≤⁺ y≤⊤)
...     | alg-distrib with x ⊕ y ≟ x | x ⊕ y ≟ y
...       | no  x⊕y≉x | no  x⊕y≉y = contradiction₂ (⊕-sel x y) x⊕y≉x x⊕y≉y
...       | no  x⊕y≉x | yes x⊕y≈y = isLevelPDistrib-cong k eq₁ eq₂ (pres-distrib ((toℕ i , toℕ j) ∷ s) alg-distrib)
  where
  eq₁ : valid (f ▷ x ⊕ y , (toℕ i , toℕ j) ∷ s) ≈⁺ f ▷⁺ (valid (x ⊕ y , s))
  eq₁ = ≈⁺-sym (▷⁺-accept f▷x⊕y≉∞ ij⇿s (i∉s ∘ just))

  eq₂ : valid ((f ▷ x) ⊕ (f ▷ y) , (toℕ i , toℕ j) ∷ s) ≈⁺ (f ▷⁺ valid (x , r)) ⊕⁺ (f ▷⁺ valid (y , s))
  eq₂ = {!!}
  
...       | yes x⊕y≈x | no  x⊕y≉y = isLevelPDistrib-cong k {!!} {!!} (pres-distrib ((toℕ i , toℕ j) ∷ r) alg-distrib)
...       | yes x⊕y≈x | yes x⊕y≈y = isLevelPDistrib-cong k eq₁ eq₂  (pres-distrib ((toℕ i , toℕ j) ∷ (r ⊓ₗₑₓ s)) alg-distrib)
  where
  
  
  eq₁ : valid (f ▷ x ⊕ y , (toℕ i , toℕ j) ∷ (r ⊓ₗₑₓ s)) ≈⁺ f ▷⁺ valid (x ⊕ y , r ⊓ₗₑₓ s)
  eq₁ = ≈⁺-sym (▷⁺-accept f▷x⊕y≉∞ (⊓ₗₑₓ-pres-⇿ ij⇿r ij⇿s) (⊓ₗₑₓ-pres-∉ {!i∉s!} {!!}))
    where
    test : f ▷ x ⊕ y ≉ ∞#
    test f▷x⊕y≈∞ = contradiction₂ {!!} {!!} {!!}
    
  eq₂ : valid ((f ▷ x) ⊕ (f ▷ y) , (toℕ i , toℕ j) ∷ r ⊓ₗₑₓ s) ≈⁺ (f ▷⁺ valid (x , r)) ⊕⁺ (f ▷⁺ valid (y , s))
  eq₂ = ≈⁺-sym {!!}
