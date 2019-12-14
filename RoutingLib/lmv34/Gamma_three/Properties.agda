open import Algebra.FunctionProperties
open import Data.Fin using (Fin)
open import Data.Product using (_,_; _×_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.List using (List; filter; tabulate; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Membership.DecSetoid as Membership
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties
open import Data.Nat using (zero; suc; ℕ; _*_; _+_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction; contraposition; ¬?)
open import Relation.Unary using (Pred; Decidable; _⇒_)
open import Relation.Binary using (Setoid; DecSetoid; Rel; Reflexive; Symmetric; Transitive; _Respects_)
open import Relation.Binary.PropositionalEquality as PropositionalEq using (_≡_; refl; cong)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_one.Properties as Gamma_one_Properties
import RoutingLib.lmv34.Gamma_two as Gamma_two
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; RouteMapMatrix)
import RoutingLib.lmv34.Gamma_two.Properties as Gamma_two_Properties
import RoutingLib.lmv34.Gamma_three as Gamma_three
import RoutingLib.lmv34.Gamma_three.Algebra as Gamma_three_Algebra

module RoutingLib.lmv34.Gamma_three.Properties
  {a b ℓ} {alg : RawRoutingAlgebra a b ℓ}
  (isRAlg : IsRoutingAlgebra alg) {n}
  (A    : AdjacencyMatrix' alg n)
  (Imp Prot Exp : RouteMapMatrix isRAlg n )
  (A=Imp∘Prot∘Exp : IsComposition isRAlg n A Imp Prot Exp)
  where

open RawRoutingAlgebra alg
open Routing alg n renaming (I to M) using (RoutingMatrix; _≈ₘ_; ≈ₘ-refl)
open Gamma_zero alg A
open Gamma_zero_Algebra alg n
open Gamma_one isRAlg A
open Gamma_one_Algebra isRAlg n
open Gamma_one_Properties isRAlg A
open Gamma_two isRAlg Imp Prot Exp
open Gamma_two_Algebra isRAlg n 
open Gamma_two_Properties isRAlg A Imp Prot Exp A=Imp∘Prot∘Exp
  hiding (≈ₛ-refl; ≈ₛ-sym; ≈ₛ-trans; 𝕊ₛ)
  renaming (_≈ₛ_ to _≈ₛ,₂_)
open Gamma_three isRAlg Imp Prot Exp
open Gamma_three_Algebra isRAlg n

open DecSetoid FinRoute-decSetoid using () renaming (_≈_ to _≈ᵣ_; refl to ≈ᵣ-refl; trans to ≈ᵣ-trans; sym to ≈ᵣ-sym; _≟_ to _≟ᵣ_)
open Membership FinRoute-decSetoid using (_∈?_; _∈_; _∉_)
open PermutationProperties FinRoute-setoid using (++⁺; ++-identityˡ; ++-identityʳ; ++-assoc)

------------------------------------
-- Γ₃-State
infix 2 _≈ₛ_

_≈ₛ_ : Rel Γ₃-State (a ⊔ ℓ)
(S₃ V O I ∇,Δ) ≈ₛ (S₃ V' O' I' ∇,Δ') =
  V ≈ᵥ V'   ×
  O ≈ᵥ,₂ O' ×
  I ≈ᵥ,₂ I' ×
  π₁ ∇,Δ ≈ᵥ,₂ π₁ ∇,Δ' ×
  π₂ ∇,Δ ≈ᵥ,₂ π₂ ∇,Δ'

≈ₛ-refl : Reflexive _≈ₛ_
≈ₛ-refl = (≈ᵥ-refl , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl)
≈ₛ-sym : Symmetric _≈ₛ_
≈ₛ-sym (V=V' , I=I' , O=O' , ∇=∇' , Δ=Δ') =
  (≈ᵥ-sym V=V' , ≈ᵥ,₂-sym I=I' , ≈ᵥ,₂-sym O=O' , ≈ᵥ,₂-sym ∇=∇' , ≈ᵥ,₂-sym Δ=Δ')
≈ₛ-trans : Transitive _≈ₛ_
≈ₛ-trans (V=V' , I=I' , O=O' , ∇=∇' , Δ=Δ') (V'=V'' , I'=I'' , O'=O'' , ∇'=∇'' , Δ'=Δ'') =
  (≈ᵥ-trans V=V' V'=V'' , ≈ᵥ,₂-trans I=I' I'=I'' , ≈ᵥ,₂-trans O=O' O'=O'' , ≈ᵥ,₂-trans ∇=∇' ∇'=∇'' , ≈ᵥ,₂-trans Δ=Δ' Δ'=Δ'')
  
𝕊ₛ : Setoid a (a ⊔ ℓ)
𝕊ₛ = record {Carrier = Γ₃-State;
             _≈_ = _≈ₛ_;
             isEquivalence =
               record {refl = ≈ₛ-refl; sym = ≈ₛ-sym; trans = ≈ₛ-trans}}


------------------------------------
-- Operation properties

-- lmv34: Couldn't find bi-implication in the stdlib
infix 4 _⇔_
_⇔_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ⇔ Q = λ x → (P x → Q x) × (Q x → P x)

filter-lemma : ∀ {p} {P P' : Pred (Fin n × Route) p} {P? : Decidable P} {P?' : Decidable P'}
               xs → (∀ x → (P ⇔ P') x) → filter P? xs ↭ filter P?' xs
filter-lemma [] P=P' = ↭-refl
filter-lemma {P? = P?} {P?' = P?'} (x ∷ xs) P=P' with P? x | P?' x
... | yes _  | yes _    = prep ≈ᵣ-refl (filter-lemma xs P=P')
... | yes Px | no ¬P'x  = contradiction ((π₁ (P=P' x)) Px) ¬P'x
... | no ¬Px | yes P'x  = contradiction ((π₂ (P=P' x)) P'x) ¬Px
... | no _   | no _     = filter-lemma xs P=P'

∈-congₗ : ∀ {xs x y} → x ≈ᵣ y → x ∈ xs → y ∈ xs
∈-congₗ {[]} _ ()
∈-congₗ {x' ∷ xs} x=y (here px) = here (≈ᵣ-trans (≈ᵣ-sym x=y) px)
∈-congₗ {x' ∷ xs} x=y (there x∈xs) = there (∈-congₗ x=y x∈xs)

∈-congᵣ : ∀ {x xs ys} → xs ↭ ys → x ∈ xs → x ∈ ys
∈-congᵣ refl x∈xs = x∈xs
∈-congᵣ (prep x₁=y₁ xs=ys) (here x=x₁) = here (≈ᵣ-trans x=x₁ x₁=y₁)
∈-congᵣ (prep x₁=y₁ xs=ys) (there x∈xs) = there (∈-congᵣ xs=ys x∈xs)
∈-congᵣ (swap x₁=y₂ x₂=y₁ xs=ys) (here x=x₁) = there (here (≈ᵣ-trans x=x₁ x₁=y₂))
∈-congᵣ (swap x₁=y₂ x₂=y₁ xs=ys) (there (here x=x₂)) = here (≈ᵣ-trans x=x₂ x₂=y₁)
∈-congᵣ (swap x₁=y₂ x₂=y₁ xs=ys) (there (there x∈xs)) = there (there (∈-congᵣ xs=ys x∈xs))
∈-congᵣ (trans xs=ys ys=zs) x∈xs = ∈-congᵣ ys=zs (∈-congᵣ xs=ys x∈xs)

minus-respects-≈ᵣ : ∀ {xs} → (λ x → ¬ (x ∈ xs)) Respects _≈ᵣ_
minus-respects-≈ᵣ {[]} {y} {y'} y=y' Py = λ ()
minus-respects-≈ᵣ {(x ∷ xs)} {y} {y'} y=y' Py with y' ∈? (x ∷ xs)
... | yes (here y'=x) = contradiction (here (≈ᵣ-trans y=y' y'=x)) Py
... | yes (there Py') = contradiction (there (∈-congₗ (≈ᵣ-sym y=y') Py')) Py
... | no ¬Py' = ¬Py'

minus-congₗ : LeftCongruent _↭_ _-_
minus-congₗ {A} B=B' = filter-lemma A (λ x → (contraposition (∈-congᵣ (↭-sym B=B'))) , (contraposition (∈-congᵣ B=B')))

minus-congᵣ : RightCongruent _↭_ _-_
minus-congᵣ A=A' = filter-cong minus-respects-≈ᵣ A=A'

minus-cong : Congruent₂ _↭_ _-_
minus-cong {A} {A'} {B} {B'} A=A' B=B' = begin
  A - B ↭⟨ minus-congᵣ A=A' ⟩
  A' - B ↭⟨ minus-congₗ {A'} B=B' ⟩
  A' - B' ∎
  where open PermutationReasoning

minusᵥ-cong : Congruent₂ _≈ᵥ,₂_ _-ᵥ_
minusᵥ-cong {U} {U'} {V} {V'} U=U' V=V' i j = minus-cong (U=U' i j) (V=V' i j)

minus-zeroₗ : LeftZero _↭_ Ø _-_
minus-zeroₗ xs = ↭-refl

minus-identityᵣ : RightIdentity _↭_ Ø _-_
minus-identityᵣ [] = ↭-refl
minus-identityᵣ (x ∷ xs) = prep ≈ᵣ-refl (minus-identityᵣ xs)

∪-cong : Congruent₂ _↭_ _∪_
∪-cong A=A' B=B' = ++⁺ A=A' (minus-cong B=B' A=A')

∪-identityₗ : LeftIdentity _↭_ Ø _∪_
∪-identityₗ xs = minus-identityᵣ xs

∪-identityᵣ : RightIdentity _↭_ Ø _∪_
∪-identityᵣ xs = ++-identityʳ xs

∪ᵥ-cong : Congruent₂ _≈ᵥ,₂_ _∪ᵥ_
∪ᵥ-cong U=U' V=V' i j = ∪-cong (U=U' i j) (V=V' i j)

diff-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
            π₁ (diff A B) ↭ π₁ (diff A' B') ×
            π₂ (diff A B) ↭ π₂ (diff A' B')
diff-cong A=A' B=B' = minus-cong A=A' B=B' , minus-cong B=B' A=A'

diffᵥ-cong : ∀ {U U' V V'} → U ≈ᵥ,₂ U' → V ≈ᵥ,₂ V' →
            π₁ (diffᵥ U V) ≈ᵥ,₂ π₁ (diffᵥ U' V') ×
            π₂ (diffᵥ U V) ≈ᵥ,₂ π₂ (diffᵥ U' V')
diffᵥ-cong A=A' B=B' =
  (λ i j → minus-cong (A=A' i j) (B=B' i j)) ,
  (λ i j → minus-cong (B=B' i j) (A=A' i j))

Γ₃,ᵥ-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → Γ₃,ᵥ I ≈ᵥ Γ₃,ᵥ I'
Γ₃,ᵥ-cong = Γ₂,ᵥ-cong

Γ₃,ᵢ-cong : ∀ {I I' ∇ ∇' Δ Δ'} → I ≈ᵥ,₂ I' → ∇ ≈ᵥ,₂ ∇' → Δ ≈ᵥ,₂ Δ' →
            Γ₃,ᵢ I (∇ , Δ) ≈ᵥ,₂ Γ₃,ᵢ I' (∇' , Δ')
Γ₃,ᵢ-cong I=I' ∇=∇' Δ=Δ' = ∪ᵥ-cong (minusᵥ-cong I=I' (Γ₂,ᵢ-cong ∇=∇')) (Γ₂,ᵢ-cong Δ=Δ')

Γ₃,ₒ-cong : ∀ {V V'} → V ≈ᵥ V' → Γ₃,ₒ V ≈ᵥ,₂ Γ₃,ₒ V'
Γ₃,ₒ-cong = Γ₂,ₒ-cong

Γ₃,ₓ-cong : ∀ {V V' O O'} → V ≈ᵥ V' → O ≈ᵥ,₂ O' →
            (π₁ (Γ₃,ₓ V O) ≈ᵥ,₂ π₁(Γ₃,ₓ V' O')) ×
            (π₂ (Γ₃,ₓ V O) ≈ᵥ,₂ π₂(Γ₃,ₓ V' O'))
Γ₃,ₓ-cong V=V' O=O' = diffᵥ-cong O=O' (Γ₃,ₒ-cong V=V')

Γ₃-cong : Congruent₁ _≈ₛ_ Γ₃
Γ₃-cong (V=V' , I=I' , O=O' , ∇=∇' , Δ=Δ') = 
  Γ₃,ᵥ-cong I=I' ,
  Γ₃,ᵢ-cong I=I' ∇=∇' Δ=Δ' ,
  Γ₃,ₒ-cong V=V' ,
  π₁ (Γ₃,ₓ-cong V=V' O=O') ,
  π₂ (Γ₃,ₓ-cong V=V' O=O')

------------------------------------
-- Theorems

-- diff-lemma is false as it is. Take for example A = {0, 0}, B = {0}.
-- What we need is:
  -- A and B have no duplicates.
postulate
  diff-lemma : ∀ A B → let (∇ , Δ) = diff A B in
          (A - ∇) ∪ Δ ↭ B

-- map-distrib is false as it is. Take for example f(x) = (0, ∞), X = {(0,0)}, Y = {(0,∞)}.
-- What we need is:
  -- Y ⊆ X, and
  -- f is an injective function, or:
    -- f only acts on the second projection of the elements in X and Y (leaving the first unchanged), and
    -- X and Y have unique destinations (no two (d, s) and (d, s') with s≠s').
postulate
  map-distrib : ∀ {f} {X} {Y} → map₂ f (X - Y) ↭ (map₂ f X) - (map₂ f Y)

∈-†-lemma₁ : ∀ {X d v} → (d , v) ∈ X → ¬(v ≈ ∞#) → (d , v) ∈ X †
∈-†-lemma₁ {(d' , v') ∷ X} (here (d=d' , v=v')) v≠∞ with v' ≟ ∞#
... | yes v'=∞ = contradiction (≈-trans v=v' v'=∞) v≠∞
... | no _     = here (d=d' , v=v')
∈-†-lemma₁ {(d' , v') ∷ X} (there dv∈X) v≠∞ with v' ≟ ∞#
... | yes v'=∞ = ∈-†-lemma₁ dv∈X v≠∞
... | no _     = there (∈-†-lemma₁ dv∈X v≠∞)

∈-†-lemma₂ : ∀ {X d v} → (d , v) ∈ X † → (d , v) ∈ X
∈-†-lemma₂ {((d' , v') ∷ X)} dv∈X† with v' ≟ ∞#
... | yes _ = there (∈-†-lemma₂ {X} dv∈X†)
∈-†-lemma₂ {(d' , v') ∷ X} {d} {v} (here dv=dv') | no _ = here dv=dv'
∈-†-lemma₂ {(d' , v') ∷ X} {d} {v} (there dv∈X†) | no _ = there (∈-†-lemma₂ dv∈X†)

†-distrib : ∀ {X Y} → (X - Y) † ↭ (X †) - (Y †)
†-distrib {[]} {Y} = ↭-refl
†-distrib {(d , v) ∷ X} {Y} with (d , v) ∈? Y
... | yes dv∈Y = prf
  where prf : (X - Y) † ↭ (((d , v) ∷ X) †) - (Y †)
        prf with v ≟ ∞#
        ... | yes _  = †-distrib {X} {Y}
        ... | no v≠∞ = prf'
          where prf' : (X - Y) † ↭ ((d , v) ∷ (X †)) - (Y †)
                prf' with (d , v) ∈? Y †
                ... | yes _    = †-distrib {X} {Y}
                ... | no dv∉Y† = contradiction (∈-†-lemma₁ dv∈Y v≠∞) dv∉Y†
... | no dv∉Y  = prf
  where prf : ((d , v) ∷ (X - Y)) † ↭ ((d , v) ∷ X) † - Y †
        prf with v ≟ ∞#
        ... | yes _ = †-distrib {X} {Y}
        ... | no _  = prf'
          where prf' : (d , v) ∷ ((X - Y) †) ↭ ((d , v) ∷ (X †)) - Y †
                prf' with (d , v) ∈? Y †
                ... | yes dv∈Y† = contradiction dv∈Y† (contraposition ∈-†-lemma₂ dv∉Y)
                ... | no _      = prep ((refl , ≈-refl)) (†-distrib {X} {Y})

-- Lemma A.6
f-minus-distrib : ∀ f X Y  → f [ X - Y ] ↭ f [ X ] - f [ Y ] 
f-minus-distrib f X Y = begin
                 f [ X - Y ]                     ≡⟨⟩
                 (map₂ f (X - Y)) †              ↭⟨ †-cong (map-distrib {X = X}) ⟩
                 ((map₂ f X) - (map₂ f Y)) †     ↭⟨ †-distrib {X = (map₂ f X)} ⟩
                 ((map₂ f X) †) - ((map₂ f Y) †) ≡⟨⟩
                 f [ X ] - f [ Y ] 
                 ∎
                 where open PermutationReasoning

F-minus-distrib : ∀ F O O'  → (F 〖 O -ᵥ O' 〗) ≈ᵥ,₂ ((F 〖 O  〗) -ᵥ (F 〖 O' 〗))
F-minus-distrib F O O' i j = begin
                     (F 〖 O -ᵥ O' 〗) i j                      ↭⟨ ↭-refl ⟩
                     (F i j) [ (O -ᵥ O') j i ]                  ↭⟨ ↭-refl ⟩
                     (F i j) [ (O j i) - (O' j i) ]             ↭⟨ f-minus-distrib (F i j) (O j i) (O' j i) ⟩
                     ((F i j) [ O j i ]) - ((F i j) [ O' j i ]) ↭⟨ ↭-refl ⟩
                     ((F 〖 O 〗) i j) - ((F 〖 O' 〗) i j)     ↭⟨ ↭-refl ⟩
                     ((F 〖 O 〗) -ᵥ (F 〖 O' 〗)) i j 
                     ∎
                     where open PermutationReasoning

Γ₂,ᵢ-distrib : ∀ O O' → Γ₂,ᵢ (O -ᵥ O') ≈ᵥ,₂ (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (O'))
Γ₂,ᵢ-distrib O O' i j = begin
                       (Γ₂,ᵢ (O -ᵥ O')) i j                                               ↭⟨ ↭-refl ⟩
                       ((Imp ●ₘ Prot) 〖 O -ᵥ O' 〗) i j                                 ↭⟨ F-minus-distrib (Imp ●ₘ Prot) O O' i j ⟩
                       (((Imp ●ₘ Prot) 〖 O  〗) i j) - (((Imp ●ₘ Prot) 〖 O' 〗) i j)  ↭⟨ ↭-refl ⟩                       
                       ((Γ₂,ᵢ (O)) i j) - ((Γ₂,ᵢ (O')) i j)                               ↭⟨ ↭-refl ⟩
                       (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (O')) i j 
                       ∎
                       where open PermutationReasoning

-- To show relationship of Γ₃ and Γ₂ 
-- we simply need an invariant, so that we can equate each step of Γ₃ with a step of Γ₂.
-- We only need to ensure that at each step the I component of Γ₃ is equal to the I component of Γ₂.
-- Then the V, I, and O components will be the same at each step.

Γ₃-invariant : Γ₃-State → Set (a ⊔ ℓ)
Γ₃-invariant (S₃ V I O (∇ , Δ)) = Γ₂,ᵢ O ≈ᵥ,₂ Γ₃,ᵢ I  (∇ , Δ)

lemma1 : ∀ X Y → ((X -ᵥ (X -ᵥ Y)) ∪ᵥ (Y -ᵥ X)) ≈ᵥ,₂ Y 
lemma1 X Y i j = begin
                 ((X -ᵥ (X -ᵥ Y)) ∪ᵥ (Y -ᵥ X)) i j                       ↭⟨ ↭-refl ⟩                                        
                 ((X -ᵥ (X -ᵥ Y)) i j) ∪ ((Y -ᵥ X) i j)                  ↭⟨ ↭-refl ⟩                                        
                 ((X i j) - ((X i j) - (Y i j))) ∪ ((Y i j) - (X i j))  ↭⟨ diff-lemma (X i j) (Y i j) ⟩                                
                 Y i j 
                 ∎
                 where open PermutationReasoning


Γ₃-invariant-maintained : ∀ (S : Γ₃-State) → Γ₃-invariant S → Γ₃-invariant (Γ₃ S) 
Γ₃-invariant-maintained (S₃ V I O (∇ , Δ)) inv = prf
   where
     prf : Γ₂,ᵢ (Γ₂,ₒ V) ≈ᵥ,₂ Γ₃,ᵢ (Γ₃,ᵢ I  (∇ , Δ))  (diffᵥ O (Γ₃,ₒ V))
     prf = begin
             Γ₂,ᵢ (Γ₂,ₒ V)                                                       ≈⟨ ≈ᵥ,₂-sym (lemma1 ((Γ₂,ᵢ O)) ((Γ₂,ᵢ (Γ₂,ₒ V)))) ⟩
             ((Γ₂,ᵢ O) -ᵥ (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (Γ₂,ₒ V))) ∪ᵥ (Γ₂,ᵢ (Γ₂,ₒ V) -ᵥ (Γ₂,ᵢ O)) ≈⟨ ≈ᵥ,₂-refl  ⟩                    
             ((Γ₂,ᵢ O) -ᵥ (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (Γ₃,ₒ V))) ∪ᵥ (Γ₂,ᵢ (Γ₃,ₒ V) -ᵥ (Γ₂,ᵢ O)) ≈⟨ ∪ᵥ-cong {x = ((Γ₂,ᵢ O) -ᵥ (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (Γ₃,ₒ V)))}  {u = (Γ₂,ᵢ (Γ₃,ₒ V) -ᵥ (Γ₂,ᵢ O))} ((minusᵥ-cong {Γ₂,ᵢ O}  ≈ᵥ,₂-refl (≈ᵥ,₂-sym (Γ₂,ᵢ-distrib O (Γ₃,ₒ V))))) ≈ᵥ,₂-refl  ⟩   
             ((Γ₂,ᵢ O) -ᵥ (Γ₂,ᵢ (O -ᵥ (Γ₃,ₒ V)))) ∪ᵥ (Γ₂,ᵢ (Γ₃,ₒ V) -ᵥ (Γ₂,ᵢ O))     ≈⟨ ∪ᵥ-cong ≈ᵥ,₂-refl ((≈ᵥ,₂-sym ((Γ₂,ᵢ-distrib (Γ₃,ₒ V) O))))  ⟩
             ((Γ₂,ᵢ O) -ᵥ (Γ₂,ᵢ (O -ᵥ (Γ₃,ₒ V)))) ∪ᵥ (Γ₂,ᵢ ((Γ₃,ₒ V) -ᵥ O)) ≈⟨ ≈ᵥ,₂-refl  ⟩                                       
             Γ₃,ᵢ (Γ₂,ᵢ O)  (O -ᵥ (Γ₃,ₒ V) , (Γ₃,ₒ V) -ᵥ O)               ≈⟨ ≈ᵥ,₂-refl ⟩                          
             Γ₃,ᵢ (Γ₂,ᵢ O)  (O -ᵥ (Γ₃,ₒ V) , (Γ₃,ₒ V) -ᵥ O)               ≈⟨ Γ₃,ᵢ-cong {I = (Γ₂,ᵢ O)} {∇ = (O -ᵥ (Γ₃,ₒ V))} {Δ = ((Γ₃,ₒ V) -ᵥ O)}  inv ≈ᵥ,₂-refl ≈ᵥ,₂-refl  ⟩
             Γ₃,ᵢ ((Γ₃,ᵢ I  (∇ , Δ)))  (O -ᵥ (Γ₃,ₒ V) , (Γ₃,ₒ V) -ᵥ O)   ≈⟨ ≈ᵥ,₂-refl ⟩                                       
             Γ₃,ᵢ (Γ₃,ᵢ I  (∇ , Δ))  (diffᵥ O (Γ₃,ₒ V))
            ∎
            where open EqReasoning 𝕍₂ₛ

Γ₃-invariant-maintained-iter : ∀ (S : Γ₃-State) k → Γ₃-invariant S → Γ₃-invariant ((Γ₃ ^ k) S) 
Γ₃-invariant-maintained-iter S zero inv = inv 
Γ₃-invariant-maintained-iter S (suc k) inv = Γ₃-invariant-maintained ((Γ₃ ^ k) S) (Γ₃-invariant-maintained-iter S k inv)  


S₃≈S₂ : Γ₃-State → Γ₂-State → Set (a ⊔ ℓ)
S₃≈S₂ (S₃ V I O (∇ , Δ)) (S₂ V' I' O') = (S₂ V I O) ≈ₛ,₂ (S₂ V' I' O')

S₃≈S₂-maintained : ∀ (S3 : Γ₃-State) (S2 : Γ₂-State) → S₃≈S₂ S3 S2 → Γ₃-invariant S3 → S₃≈S₂ (Γ₃ S3) (Γ₂ S2)
S₃≈S₂-maintained  (S₃ V I O (∇ , Δ)) (S₂ V' I' O') ( V≈V' , (I≈I' , O≈O') ) inv = prfV , (prfI , prfO)
  where
    prfV : (Γ₃,ᵥ I) ≈ᵥ (Γ₂,ᵥ I')
    prfV = Γ₂,ᵥ-cong I≈I'

    prfI : (Γ₃,ᵢ I (∇ , Δ)) ≈ᵥ,₂ (Γ₂,ᵢ O')
    prfI = begin
            Γ₃,ᵢ I (∇ , Δ)  ≈⟨ ≈ᵥ,₂-sym inv ⟩             
            Γ₂,ᵢ O          ≈⟨ Γ₂,ᵢ-cong O≈O' ⟩             
            Γ₂,ᵢ O' 
            ∎
            where open EqReasoning 𝕍₂ₛ

    prfO : (Γ₃,ₒ V) ≈ᵥ,₂ (Γ₂,ₒ V')
    prfO = Γ₂,ₒ-cong V≈V'  


S₃≈S₂-maintained-iter : ∀ (S3 : Γ₃-State) (S2 : Γ₂-State) k → S₃≈S₂ S3 S2 → Γ₃-invariant S3 → S₃≈S₂ ((Γ₃ ^ k) S3) ((Γ₂ ^ k) S2)
S₃≈S₂-maintained-iter S3 S2 zero eq inv = eq 
S₃≈S₂-maintained-iter S3 S2 (suc k) eq inv =
   S₃≈S₂-maintained ((Γ₃ ^ k) S3) ((Γ₂ ^ k) S2) (S₃≈S₂-maintained-iter S3 S2 k eq inv)  (Γ₃-invariant-maintained-iter S3 k inv) 

S₃≈S₂-init : S₃≈S₂ (S₃ (~ M) Øᵥ,₂ Øᵥ,₂ (Øᵥ,₂ , Øᵥ,₂)) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂)
S₃≈S₂-init = ≈ᵥ-refl , ( ≈ᵥ,₂-refl , ≈ᵥ,₂-refl )

Γ₂,ᵢØ≈Ø : Γ₂,ᵢ Øᵥ,₂ ≈ᵥ,₂ Øᵥ,₂
Γ₂,ᵢØ≈Ø i j = ↭-refl 

Ø∪Ø≈Ø : (Øᵥ,₂ ∪ᵥ Øᵥ,₂) ≈ᵥ,₂ Øᵥ,₂
Ø∪Ø≈Ø i j = ↭-refl 

Ø-Ø≈Ø : (Øᵥ,₂ -ᵥ Øᵥ,₂) ≈ᵥ,₂ Øᵥ,₂
Ø-Ø≈Ø i j = ↭-refl 

init-invariant : Γ₃-invariant (S₃ (~ M) Øᵥ,₂ Øᵥ,₂ (Øᵥ,₂ , Øᵥ,₂))
init-invariant  = prf
  where
    prf : Γ₂,ᵢ Øᵥ,₂ ≈ᵥ,₂ Γ₃,ᵢ Øᵥ,₂  (Øᵥ,₂ , Øᵥ,₂)
    prf = ≈ᵥ,₂-refl
         
S₃≈S₂-maintained-init : ∀ k → S₃≈S₂ ((Γ₃ ^ k) (S₃ (~ M) Øᵥ,₂ Øᵥ,₂ (Øᵥ,₂ , Øᵥ,₂))) ((Γ₂ ^ k) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂))
S₃≈S₂-maintained-init  k = S₃≈S₂-maintained-iter (S₃ (~ M) Øᵥ,₂ Øᵥ,₂ (Øᵥ,₂ , Øᵥ,₂)) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂) k S₃≈S₂-init init-invariant

-- now, related gamma-3 to gamma-1 and gamma-0 ... 
