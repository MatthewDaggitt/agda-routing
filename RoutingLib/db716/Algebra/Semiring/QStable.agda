open import Algebra using (Semiring)
open import Data.Fin using (_≟_; Fin; toℕ)
open import Data.List using (List; []; _∷_; length; _++_; zip; foldr; map)
open import Data.List.Properties using (map-++-commute)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate; lookup)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there; tail; satisfied)
open import Data.List.Relation.Unary.Any.Properties using (concat⁺; map⁻)
open import Data.List.Membership.DecPropositional using (_∈?_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Nat using (ℕ; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; <⇒≤pred; ≤-trans)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; cong to ≡-cong; cong₂ to ≡-cong₂; trans to ≡-trans)

open import RoutingLib.db716.Algebra.Semiring
open import RoutingLib.db716.Data.Path.UncertifiedFinite.Properties using (path-len-induction; path-len-induction'; all-≤k-length-paths-from-to-correct)

module RoutingLib.db716.Algebra.Semiring.QStable where

module _ {c ℓ} (S : Semiring c ℓ) where
  open Semiring S
  
  stableElement : ℕ → Carrier → Set ℓ
  stableElement q x = powSum S x (suc q) ≈ powSum S x q

module _ where
  open Semiring

  stableSemiring : ∀ {c ℓ} → ℕ → Semiring c ℓ → Set _
  stableSemiring {c} {ℓ} q S = ∀ (s : Carrier S) → stableElement S q s

module _ {c ℓ} (S : Semiring c ℓ)  where
  open Semiring S
  open import Algebra.Definitions _≈_ using (Idempotent; _IdempotentOn_)

  open import RoutingLib.db716.Algebra.SemiringMatrix S
  open import RoutingLib.db716.Data.Path.UncertifiedFinite
  open import RoutingLib.db716.Data.Path.UncertifiedFinite.Properties
  open import RoutingLib.db716.Data.Path.FindLoop
  open import RoutingLib.db716.Data.Path.UncertifiedFinite.CutLoop.Properties
  open import RoutingLib.db716.Data.Path.UncertifiedFinite.Weights S
  open import RoutingLib.db716.Results.MatrixPowers S
  open import RoutingLib.db716.Results.MatrixPowerSums S
  open import RoutingLib.Data.Matrix using (Matrix; SquareMatrix)

  loopWeightAux : ∀ {n} (m : SquareMatrix Carrier n) (e : Edge n) (p : Path n) → e ∈ p → Carrier
  loopWeightAux m e (e' ∷ p) (here e≡e') = edgeWeight m e'
  loopWeightAux m e (e' ∷ p) (there e∈p) = edgeWeight m e' * loopWeightAux m e p e∈p

  loopWeight : ∀ {n} (p : Path n) (m : SquareMatrix Carrier n) (loop : HasLoop p) → Carrier
  loopWeight ((i , i) ∷ p) m trivial = m i i
  loopWeight {n} ((i , j) ∷ p) m (here {_} {k} ki∈p) = m i j * loopWeightAux m (k , i) p ki∈p
  loopWeight (e ∷ p) m (there loop) = loopWeight p m loop

  factoriseLoopAux : ∀ {n} (m : SquareMatrix Carrier n) (e : Edge n) (p : Path n) (e∈p : e ∈ p)
    → weight m p ≈ loopWeightAux m e p e∈p * weight m (cutLoopAux e p e∈p) 
  factoriseLoopAux m e (e' ∷ p) (here e≡e') = refl
  factoriseLoopAux m e ((i , j) ∷ p) (there e∈p) = trans (*-cong refl (factoriseLoopAux m e p e∈p)) (sym (*-assoc _ _ _))
  
  factoriseLoop1 : ∀ {n} (p : Path n) (m : SquareMatrix Carrier n) (loop : HasLoop p)
    → ∃₂ λ w1 w2 → w1 * w2 ≈ weight m (cutLoop p loop) × weight m p ≈ w1 * (loopWeight p m loop) * w2
  factoriseLoop1 {n} ((i , i) ∷ p) m trivial
    = 1# , weight m p , *-identityˡ _ , sym (trans (*-assoc _ _ _) (*-identityˡ _))
  factoriseLoop1 {n} ((i , j) ∷ (k , l) ∷ p) m (here {_} {a} ai∈p)
    = 1# , weight m (cutLoop ((i , j) ∷ (k , l) ∷ p) (here ai∈p)) , *-identityˡ _ , proof
    where
      proof = begin
        m i j * (weight m ((k , l) ∷ p))
          ≈⟨ *-cong refl (factoriseLoopAux m (a , i) ((k , l) ∷ p) ai∈p) ⟩
        m i j * ((loopWeightAux m (a , i) ((k , l) ∷ p) ai∈p) * (weight m (cutLoopAux (a , i) ((k , l) ∷ p) ai∈p)))
          ≈˘⟨ *-identityˡ _ ⟩
        1# * (m i j * ((loopWeightAux m (a , i) ((k , l) ∷ p) ai∈p) * (weight m (cutLoopAux (a , i) ((k , l) ∷ p) ai∈p))))
          ≈⟨ *-cong refl (sym (*-assoc _ _ _)) ⟩
        1# * ((m i j * (loopWeightAux m (a , i) ((k , l) ∷ p) ai∈p)) * (weight m (cutLoopAux (a , i) ((k , l) ∷ p) ai∈p)))
          ≈˘⟨ *-assoc _ _ _ ⟩
        1# * (m i j * loopWeightAux m (a , i) ((k , l) ∷ p) ai∈p) * (weight m (cutLoopAux (a , i) ((k , l) ∷ p) ai∈p))
          ≡⟨⟩
        1# * (loopWeight ((i , j) ∷ (k , l) ∷ p) m (here ai∈p)) * (weight m (cutLoop ((i , j) ∷ (k , l) ∷ p) (here ai∈p))) ∎
        where open import Relation.Binary.Reasoning.Setoid setoid
  factoriseLoop1 {n} ((i , j) ∷ p) m (there loop) =
    let w1 , w2 , w1w2≈w[cutloop] , w[p]≈w1[loop]w2 = factoriseLoop1 p m loop
    in (m i j) * w1 , w2 ,
      trans (*-assoc _ _ _) (*-cong refl w1w2≈w[cutloop]) ,
      trans (*-cong refl w[p]≈w1[loop]w2) (trans (sym (*-assoc _ _ _)) (*-cong (sym (*-assoc _ _ _)) refl))

  factoriseLoop2 : ∀ {n} (p : Path n) (m : SquareMatrix Carrier n) (loop : HasLoop p)
    → ∃₂ λ w1 w2 → w1 * w2 ≈ weight m (cutLoop p loop) × weight m p + weight m (cutLoop p loop) ≈ w1 * (loopWeight p m loop + 1#) * w2
  factoriseLoop2 {n} p m loop = w1 , w2 , w1w2≈wcut , proof
    where
      fact = factoriseLoop1 p m loop
      w1 = proj₁ fact
      w2 = proj₁ (proj₂ fact)
      w1w2≈wcut = proj₁ (proj₂ (proj₂ fact))
      wp≈w1×wloop×w2 = proj₂ (proj₂ (proj₂ fact))
      proof = begin
        weight m p + weight m (cutLoop p loop)
          ≈⟨ +-cong wp≈w1×wloop×w2 (sym w1w2≈wcut) ⟩
        w1 * loopWeight p m loop * w2 + w1 * w2
          ≈⟨ +-cong refl (*-cong (sym (*-identityʳ _)) refl) ⟩
        w1 * loopWeight p m loop * w2 + w1 * 1# * w2
          ≈˘⟨ distribʳ _ _ _ ⟩
        (w1 * loopWeight p m loop + w1 * 1#) * w2
          ≈⟨ *-cong (sym (distribˡ _ _ _)) refl ⟩
        (w1 * (loopWeight p m loop + 1#)) * w2
          ≡⟨⟩
        w1 * (loopWeight p m loop + 1#) * w2 ∎
        where open import Relation.Binary.Reasoning.Setoid setoid

  0-stable⇒negligibleLoops : ∀ {n} (p : Path n) (m : SquareMatrix Carrier n) (loop : HasLoop p) → stableSemiring 0 S
    → weight m p + weight m (cutLoop p loop) ≈ weight m (cutLoop p loop)

  0-stable⇒negligibleLoops {n} p m loop 0stab =
    let (w1 , w2 , wcut≈w1w2 , wp+wcut≈w1×[wloop+1]×w2) = factoriseLoop2 p m loop
    in begin
      weight m p + weight m (cutLoop p loop)
        ≈⟨ wp+wcut≈w1×[wloop+1]×w2 ⟩
      w1 * (loopWeight p m loop + 1#) * w2
        ≈⟨ *-cong (*-cong refl (+-comm _ _)) refl ⟩
      w1 * (1# + loopWeight p m loop) * w2
        ≈⟨ *-cong (*-cong refl (0stab _)) refl ⟩
      w1 * 1# * w2
        ≈⟨ *-cong (*-identityʳ _) refl ⟩
      w1 * w2
        ≈⟨ wcut≈w1w2 ⟩
      weight m (cutLoop p loop) ∎
      where open import Relation.Binary.Reasoning.Setoid setoid

  0-stable⇒+Idempotent : stableSemiring 0 S  → Idempotent _+_
  0-stable⇒+Idempotent 0stab x = begin
    x + x
      ≈˘⟨ +-cong (*-identityʳ x) (*-identityʳ x) ⟩
    x * 1# + x * 1#
      ≈˘⟨ distribˡ x 1# 1# ⟩
    x * (1# + 1#)
      ≈⟨ *-cong refl (0stab 1#) ⟩
    x * 1#
      ≈⟨ *-identityʳ x ⟩
    x ∎
    where open import Relation.Binary.Reasoning.Setoid setoid
