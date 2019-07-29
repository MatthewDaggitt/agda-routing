open import Algebra.FunctionProperties using (Op₂; Associative)
open import Data.Fin using (Fin)
open import Data.Product using (_,_; _×_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.List using (List; filter; tabulate; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Membership.DecSetoid as Membership
open import Data.Nat using (zero; suc; ℕ; _*_; _+_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction; contraposition; ¬?)
open import Relation.Unary using (Pred; Decidable; _⇒_)
open import Relation.Binary using (Setoid; DecSetoid; Rel; Reflexive; Symmetric; Transitive; _Respects_)
open import Relation.Binary.PropositionalEquality as PropositionalEq using (_≡_; refl; cong)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
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
open Membership FinRoute-decSetoid using (_∈?_; _∈_)

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
++-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
          A ++ B ↭ A' ++ B'
++-cong {[]} {[]} A=A' B=B'         = B=B'
++-cong {x ∷ A} {.x ∷ .A} refl B=B' = prep ≈ᵣ-refl (++-cong refl B=B') 
++-cong (trans A=A' A'=A'') B=B'    = trans (++-cong A=A' refl) (++-cong A'=A'' B=B')
++-cong (prep eq A=A') B=B'         = prep eq (++-cong A=A' B=B')
++-cong (swap eq₁ eq₂ A=A') B=B'    = swap eq₁ eq₂ (++-cong A=A' B=B')

++-identityₗ : ∀ xs → [] ++ xs ↭ xs
++-identityₗ xs = ↭-refl

++-identityᵣ : ∀ xs → xs ++ [] ↭ xs
++-identityᵣ [] = ↭-refl
++-identityᵣ (x ∷ xs) = prep ≈ᵣ-refl (++-identityᵣ xs)

++-assoc : Associative _↭_ _++_
++-assoc [] ys zs = ↭-refl
++-assoc (x ∷ xs) ys zs = prep ≈ᵣ-refl (++-assoc xs ys zs)

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

minus-respects-≈ᵣ : ∀ xs → (λ x → ¬ (x ∈ xs)) Respects _≈ᵣ_
minus-respects-≈ᵣ [] {y} {y'} y=y' Py = λ ()
minus-respects-≈ᵣ (x ∷ xs) {y} {y'} y=y' Py with y' ∈? (x ∷ xs)
... | yes (here y'=x) = contradiction (here (≈ᵣ-trans y=y' y'=x)) Py
... | yes (there Py') = contradiction (there (∈-congₗ (≈ᵣ-sym y=y') Py')) Py
... | no ¬Py' = ¬Py'

minus-congₗ : ∀ {A A' B} → A ↭ A' → A - B ↭ A' - B
minus-congₗ {A} {A'} {B} A=A' = filter-cong (minus-respects-≈ᵣ B) A=A'

minus-congᵣ : ∀ {A B B'} → B ↭ B' → A - B ↭ A - B'
minus-congᵣ {A} B=B' = filter-lemma A (λ x → (contraposition (∈-congᵣ (↭-sym B=B'))) , (contraposition (∈-congᵣ B=B')))

minus-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' → A - B ↭ A' - B'
minus-cong {A} {A'} {B} {B'} A=A' B=B' = begin
  A - B ↭⟨ minus-congₗ A=A' ⟩
  A' - B ↭⟨ minus-congᵣ {A'} B=B' ⟩
  A' - B' ∎
  where open PermutationReasoning

minusᵥ-cong : ∀ {U U' V V'} → U ≈ᵥ,₂ U' → V ≈ᵥ,₂ V' →
          (U -ᵥ V) ≈ᵥ,₂ (U' -ᵥ V')
minusᵥ-cong U=U' V=V' i j = minus-cong (U=U' i j) (V=V' i j)

[]-xs : ∀ xs → [] - xs ↭ []
[]-xs xs = ↭-refl

xs-[] : ∀ xs → xs - [] ↭ xs
xs-[] [] = ↭-refl
xs-[] (x ∷ xs) = prep ≈ᵣ-refl (xs-[] xs)

∪-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
         A ∪ B ↭ A' ∪ B'
∪-cong {A} {A'} {B} {B'} A=A' B=B' = ++-cong A=A' (minus-cong B=B' A=A')

∪-identityₗ : ∀ xs → [] ∪ xs ↭ xs
∪-identityₗ xs = xs-[] xs

∪-identityᵣ : ∀ xs → xs ∪ [] ↭ xs
∪-identityᵣ xs = ++-identityᵣ xs

∪ᵥ-cong : ∀ {U U' V V'} → U ≈ᵥ,₂ U' → V ≈ᵥ,₂ V' →
          (U ∪ᵥ V) ≈ᵥ,₂ (U' ∪ᵥ V')
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

Γ₃-cong : ∀ {S S'} → S ≈ₛ S' → Γ₃ S ≈ₛ Γ₃ S'
Γ₃-cong (V=V' , I=I' , O=O' , ∇=∇' , Δ=Δ') = 
  Γ₃,ᵥ-cong I=I' ,
  Γ₃,ᵢ-cong I=I' ∇=∇' Δ=Δ' ,
  Γ₃,ₒ-cong V=V' ,
  π₁ (Γ₃,ₓ-cong V=V' O=O') ,
  π₂ (Γ₃,ₓ-cong V=V' O=O')

------------------------------------
-- Theorems

postulate
  -- Lemma A.5
  F-union-cong : ∀ (f : Route → Route) → (A B : RoutingSet)
                 → f [ A ∪ B ] ↭ f [ A ] ∪ f [ B ]
  -- Lemma A.6
  F-minus-cong : ∀ (f : Route → Route) → (A B : RoutingSet)
               → f [ A - B ] ↭ f [ A ] - f [ B ]
  diff-lemma : ∀ A B → let (∇ , Δ) = diff A B in
          (A - ∇) ∪ Δ ↭ B

-- Lemma 3.3
F-diff-cong : ∀ F A B → let (∇ , Δ) = diffᵥ A B in
              ((F 〖 A 〗 -ᵥ F 〖 ∇ 〗) ∪ᵥ F 〖 Δ 〗) ≈ᵥ,₂ (F 〖 B 〗)
F-diff-cong F A B i j = let (∇ , Δ) = diffᵥ A B in begin
  ((F 〖 A 〗 -ᵥ F 〖 ∇ 〗) ∪ᵥ F 〖 Δ 〗) i j ↭⟨ ↭-refl ⟩
  ((F i j) [ A j i ] - (F i j) [ ∇ j i ]) ∪ (F i j) [ Δ j i ]
    ↭⟨ ∪-cong {A = ((F i j) [ A j i ] - (F i j) [ ∇ j i ])}
              {A' = ((F i j) [ (A j i) - (∇ j i) ])}
              {B = (F i j) [ Δ j i ]}
              (↭-sym (F-minus-cong (F i j) (A j i) (∇ j i))) ↭-refl ⟩
  ((F i j) [ ((A j i) - (∇ j i)) ]) ∪ (F i j) [ Δ j i ]
    ↭⟨ ↭-sym (F-union-cong (F i j) ((A j i) - (∇ j i)) (Δ j i)) ⟩
  (F i j) [  ((A j i) - (∇ j i)) ∪ (Δ j i) ] ↭⟨ []-cong (diff-lemma (A j i) (B j i)) ⟩
  (F 〖 B 〗) i j ∎
  where open PermutationReasoning

postulate 
  map-distrib : ∀ {f} {X} {Y}  → map f (X - Y) ↭ (map f X) - (map f Y)

  †-distrib : ∀ {X} {Y}  → (X - Y) † ↭ (X †) - (Y †)

distrib1 : ∀ f X Y  → f [ X - Y ] ↭ f [ X ] - f [ Y ] 
distrib1 f X Y = begin
                 f [ X - Y ]                                                                      ↭⟨ ↭-refl ⟩
                 (map (λ {(d , v) → (d , f v)}) (X - Y)) †                                       ↭⟨ †-cong (map-distrib {X = X}) ⟩
                 ((map (λ {(d , v) → (d , f v)}) X) - (map (λ {(d , v) → (d , f v)}) Y)) †      ↭⟨ †-distrib {X = (map (λ {(d , v) → (d , f v)}) X)} ⟩
                 ((map (λ {(d , v) → (d , f v)}) X) †) - ((map (λ {(d , v) → (d , f v)}) Y) †)  ↭⟨ ↭-refl ⟩
                 f [ X ] - f [ Y ] 
                 ∎
                 where open PermutationReasoning

distrib2 : ∀ F O O'  → (F 〖 O -ᵥ O' 〗) ≈ᵥ,₂ ((F 〖 O  〗) -ᵥ (F 〖 O' 〗))
distrib2 F O O' i j = begin
                     (F 〖 O -ᵥ O' 〗) i j                      ↭⟨ ↭-refl ⟩
                     (F i j) [ (O -ᵥ O') j i ]                  ↭⟨ ↭-refl ⟩
                     (F i j) [ (O j i) - (O' j i) ]             ↭⟨ distrib1 (F i j) (O j i) (O' j i) ⟩
                     ((F i j) [ O j i ]) - ((F i j) [ O' j i ]) ↭⟨ ↭-refl ⟩
                     ((F 〖 O 〗) i j) - ((F 〖 O' 〗) i j)     ↭⟨ ↭-refl ⟩
                     ((F 〖 O 〗) -ᵥ (F 〖 O' 〗)) i j 
                     ∎
                     where open PermutationReasoning

Γ₂,ᵢ-distrib : ∀ O O' → Γ₂,ᵢ (O -ᵥ O') ≈ᵥ,₂ (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (O'))
Γ₂,ᵢ-distrib O O' i j = begin
                       (Γ₂,ᵢ (O -ᵥ O')) i j                                               ↭⟨ ↭-refl ⟩
                       ((Imp ●ₘ Prot) 〖 O -ᵥ O' 〗) i j                                 ↭⟨ distrib2 (Imp ●ₘ Prot) O O' i j ⟩
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
             ((Γ₂,ᵢ O) -ᵥ (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (Γ₃,ₒ V))) ∪ᵥ (Γ₂,ᵢ (Γ₃,ₒ V) -ᵥ (Γ₂,ᵢ O)) ≈⟨ ∪ᵥ-cong {U = ((Γ₂,ᵢ O) -ᵥ (Γ₂,ᵢ (O) -ᵥ Γ₂,ᵢ (Γ₃,ₒ V)))}  {V = (Γ₂,ᵢ (Γ₃,ₒ V) -ᵥ (Γ₂,ᵢ O))} ((minusᵥ-cong {U = Γ₂,ᵢ O}  ≈ᵥ,₂-refl (≈ᵥ,₂-sym (Γ₂,ᵢ-distrib O (Γ₃,ₒ V))))) ≈ᵥ,₂-refl  ⟩   
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
