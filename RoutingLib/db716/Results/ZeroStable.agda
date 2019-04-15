open import Algebra using (Semiring)

module RoutingLib.db716.Results.ZeroStable {c ℓ} (S : Semiring c ℓ) where
open Semiring S

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; length; _++_; foldr; map)
open import Data.List.Properties using (map-++-commute)
open import Data.List.All using (All; []; _∷_; tabulate; lookup)
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-reflexive; <⇒≤pred; ≤-trans)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; cong to ≡-cong)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.db716.Algebra.Semiring
open import RoutingLib.db716.Algebra.SemiringMatrix S
open import RoutingLib.db716.Data.Path.UncertifiedFinite
open import RoutingLib.db716.Data.Path.UncertifiedFinite.Properties
open import RoutingLib.db716.Data.Path.FindLoop
open import RoutingLib.db716.Data.Path.UncertifiedFinite.CutLoop.Properties
open import RoutingLib.db716.Data.Path.UncertifiedFinite.Weights S
open import RoutingLib.db716.Results.MatrixPowers S
open import RoutingLib.db716.Results.MatrixPowerSums S
open import RoutingLib.db716.Algebra.Semiring.QStable

lemma1 : ∀ {n} m xss (ys : Path n) → ys ∈ xss → stableSemiring 0 S →  best-path-weight m xss ≈ best-path-weight m xss + weight m ys

lemma1 m (xs ∷ xss) ys (here ys≡xs) 0stab = begin
  best-path-weight m (xs ∷ xss)
    ≡⟨⟩
  weight m xs + best-path-weight m xss
    ≈⟨ +-cong (sym (0-stable⇒+Idempotent S 0stab (weight m xs))) refl ⟩
  weight m xs + weight m xs + best-path-weight m xss
    ≈⟨ +-assoc _ _ _ ⟩
  weight m xs + (weight m xs + best-path-weight m xss)
    ≈⟨ +-comm _ _ ⟩
  weight m xs + best-path-weight m xss + weight m xs
    ≈⟨ +-cong refl (reflexive (≡-cong (weight m) (≡-sym ys≡xs))) ⟩
  best-path-weight m (xs ∷ xss) + weight m ys ∎
  where open import Relation.Binary.EqReasoning setoid
  
lemma1 m (xs ∷ xss) ys (there ys∈xss) 0stab = begin
  best-path-weight m (xs ∷ xss)
    ≡⟨⟩
  weight m xs + best-path-weight m xss
    ≈⟨ +-cong refl (lemma1 m xss ys ys∈xss 0stab) ⟩
  weight m xs + (best-path-weight m xss + weight m ys)
    ≈⟨ sym (+-assoc _ _ _) ⟩
  weight m xs + best-path-weight m xss + weight m ys
    ≡⟨⟩
  best-path-weight m (xs ∷ xss) + weight m ys ∎
  where open import Relation.Binary.EqReasoning setoid



lemma2 : ∀ {n k m i j ys} → PathFrom i ys → PathTo j ys → length ys ≤ k → ValidPath ys → stableSemiring 0 S
  → best-path-weight m (all-≤k-length-paths-from-to n k i j) ≈ best-path-weight m (all-≤k-length-paths-from-to n k i j) + weight m ys

lemma2 {n} {k} {m} {i} {j} {ys} ys:i→* ys:*→j |ys|≤k valid 0stab
  = lemma1 m (all-≤k-length-paths-from-to n k i j) ys (all-≤k-length-paths-from-to-correct |ys|≤k ys:i→* ys:*→j valid) 0stab 



lemma3 : ∀ {n k m} (i j : Fin n) yss → All (λ ys → PathFrom i ys × PathTo j ys × length ys ≤ k × ValidPath ys) yss → stableSemiring 0 S
  → best-path-weight m (all-≤k-length-paths-from-to n k i j) + best-path-weight m yss ≈ best-path-weight m (all-≤k-length-paths-from-to n k i j)

lemma3 {n} {k} {m} i j [] [] 0stab = +-identityʳ _

lemma3 {n} {k} {m} i j (ys ∷ yss) (pys ∷ pyss) 0stab =
  let (ys:i→* , ys:*→j , |ys|≤k , valid) = pys
  in begin
  best-path-weight m (all-≤k-length-paths-from-to n k i j) + best-path-weight m (ys ∷ yss)
    ≡⟨⟩
  best-path-weight m (all-≤k-length-paths-from-to n k i j) + (weight m ys + best-path-weight m yss)
    ≈⟨ sym (+-assoc _ _ _) ⟩
  best-path-weight m (all-≤k-length-paths-from-to n k i j) + weight m ys + best-path-weight m yss
    ≈⟨ +-cong (sym (lemma2 ys:i→* ys:*→j |ys|≤k valid 0stab)) refl ⟩
  best-path-weight m (all-≤k-length-paths-from-to n k i j) + best-path-weight m yss
    ≈⟨ lemma3 i j yss pyss 0stab ⟩
  best-path-weight m (all-≤k-length-paths-from-to n k i j) ∎
  where open import Relation.Binary.EqReasoning setoid



trimPath : ∀ {n i j} m → stableSemiring 0 S → (p : Path (suc n)) → PathFrom i p → PathTo j p → length p ≡ (suc n) → ValidPath p → i ≢ j →
  ∃ λ q → (PathFrom i q) × (PathTo j q) × (length q ≤ n) × (ValidPath q) × (weight m p + weight m q ≈ weight m q)

trimPath {n} {i} {j} m 0stab p p:i→* p:*→j |p|≡1+n valid i≢j =
  cutLoop p loop ,
  cutLoopFrom i j p loop p:i→* p:*→j valid i≢j ,
  cutLoopTo i j p loop p:i→* p:*→j valid i≢j  ,
  <⇒≤pred (≤-trans (cutLoopDecreasesLength p loop) (≤-reflexive |p|≡1+n))  ,
  cutLoopValid p loop valid ,
  0-stable⇒negligibleLoops S p m loop 0stab
  where
    loop = findLoop valid (≤-reflexive (≡-sym |p|≡1+n))
    


trimPathLifted : ∀ {n i j} (yss : List (Path (suc n))) m → stableSemiring 0 S
  → All (PathFrom i) yss
  → All (PathTo j) yss
  → All (λ ys → length ys ≡ suc n) yss
  → All ValidPath yss
  → i ≢ j
  → ∃ λ xss →
    All (PathFrom i) xss ×
    All (PathTo j) xss ×
    All (λ xs → length xs ≤ n) xss ×
    All ValidPath xss ×
    best-path-weight m yss + best-path-weight m xss ≈ best-path-weight m xss

trimPathLifted {n} [] m 0stab xssFrom xssTo allLen≡1+n allValid i≢j  = [] , [] , [] , [] , [] , +-identityˡ _

trimPathLifted {n} (ys ∷ yss) m 0stab (ys:i→* ∷ allFrom) (ys:*→j ∷ allTo) (|ys|≡1+n ∷ allLen≡1+n) (ysValid ∷ allValid) i≢j =
  let xs , xs:i→* , xs:*→j , |xs|≤n , valid , wys+wxs≈wxs = trimPath {n} m 0stab ys ys:i→* ys:*→j |ys|≡1+n ysValid i≢j
      xss , allFrom' , allTo' , allLen≤n , valid' , eqn = trimPathLifted yss m 0stab allFrom allTo allLen≡1+n allValid i≢j
      proof = begin
        best-path-weight m (ys ∷ yss) + best-path-weight m (xs ∷ xss)
          ≡⟨⟩
        (weight m ys + best-path-weight m yss) + (weight m xs + best-path-weight m xss)
          ≈⟨ +-cong (+-comm _ _) refl ⟩
        (best-path-weight m yss + weight m ys) + (weight m xs + best-path-weight m xss)
          ≈⟨ +-assoc _ _ _ ⟩
        best-path-weight m yss + (weight m ys + (weight m xs + best-path-weight m xss))
          ≈⟨ +-cong refl (sym (+-assoc _ _ _)) ⟩
        best-path-weight m yss + ((weight m ys + weight m xs) + best-path-weight m xss)
          ≈⟨ +-cong refl (+-cong wys+wxs≈wxs refl) ⟩
        best-path-weight m yss + (weight m xs + best-path-weight m xss)
          ≈⟨ +-cong refl (+-comm _ _ ) ⟩
        best-path-weight m yss + (best-path-weight m xss + weight m xs)
          ≈⟨ sym (+-assoc _ _ _) ⟩
        best-path-weight m yss + best-path-weight m xss + weight m xs
          ≈⟨ +-cong eqn refl ⟩
        best-path-weight m xss + weight m xs
          ≈⟨ +-comm _ _ ⟩
        weight m xs + best-path-weight m xss
          ≡⟨⟩
        best-path-weight m (xs ∷ xss) ∎
  in xs ∷ xss ,  xs:i→* ∷ allFrom' , xs:*→j ∷ allTo' , |xs|≤n ∷ allLen≤n , (valid ∷ valid') , proof
  where open import Relation.Binary.EqReasoning setoid



trim-all-n-length-paths : ∀ n (i j : Fin (suc n)) m → stableSemiring 0 S → i ≢ j → ∃ λ xss →
  All (PathFrom i) xss ×
  All (PathTo j) xss ×
  All (λ xs → length xs ≤ n) xss ×
  All ValidPath xss ×
  best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j) + best-path-weight m xss ≈ best-path-weight m xss

trim-all-n-length-paths n i j m 0stab i≢j = trimPathLifted (all-k-length-paths-from-to (suc n) (suc n) i j) m 0stab
    (k-length-paths-from-i {suc n} n i j)
    (tabulate λ {p} p∈paths → k-length-paths-to-j {suc n} n p i j p∈paths)
    (tabulate λ {p} p∈paths → k-length-paths-length (suc n) p i j p∈paths)
    (tabulate λ {p} p∈paths → k-length-paths-valid (suc n) p i j p∈paths)
    i≢j



best-path-weight-lemma : ∀ n (i j : Fin (suc n)) → stableSemiring 0 S → (m : SquareMatrix Carrier (suc n))
  → best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j)
    ≈ best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j)
    
best-path-weight-lemma n i j 0stab m with i ≟ j
... | yes i≡j = begin
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j)
      ≈⟨ +-cong (lemma1 m (all-≤k-length-paths-from-to (suc n) n i j) [] (i≡j⇒[]∈paths≤k (suc n) n i j i≡j) 0stab) refl ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + weight m [] + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j)
      ≡⟨⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + 1# + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j)
      ≈⟨ +-assoc _ _ _ ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + (1# + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j))
      ≈⟨ +-cong refl (0stab _) ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + 1#
      ≡⟨⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + weight m []
      ≈⟨ sym (lemma1 m (all-≤k-length-paths-from-to (suc n) n i j) [] (i≡j⇒[]∈paths≤k (suc n) n i j i≡j) 0stab) ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) ∎
    where open import Relation.Binary.EqReasoning setoid
... | no i≢j =
  let xss , allFrom , allTo , allLen≤n , valid , eqn = trim-all-n-length-paths n i j m 0stab i≢j
      lem3 = lemma3 {suc n} {n} {m} i j xss (tabulate λ {xs} xs∈paths →
        lookup allFrom xs∈paths ,
        lookup allTo xs∈paths ,
        lookup allLen≤n xs∈paths ,
        lookup valid xs∈paths)
        0stab
  in begin
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j)
      ≈⟨ +-cong (sym lem3) refl ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + best-path-weight m xss + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j)
      ≈⟨ +-assoc _ _ _ ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + (best-path-weight m xss + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j))
      ≈⟨ +-cong refl (+-comm _ _) ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + (best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j) + best-path-weight m xss)
      ≈⟨ +-cong refl eqn ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + best-path-weight m xss
      ≈⟨ lem3 ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) ∎
  where open import Relation.Binary.EqReasoning setoid
        open import RoutingLib.db716.Data.List.Properties.MonoidFolds +-monoid



matricesInheritStability : ∀ n → stableSemiring 0 S → stableSemiring n (SemiringMat (suc n))

matricesInheritStability 0 0stab m Fin.zero (Fin.suc ())
matricesInheritStability 0 0stab m (Fin.suc ())

matricesInheritStability 0 0stab m Fin.zero Fin.zero = 0stab _

matricesInheritStability (suc n') 0stab m i j =
  let n = suc n'
  in begin
    powSum 𝕄 m (suc n) i j
      ≈⟨ mat-pow-sums-find-best-paths (suc n) (suc n) i j m  ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) (suc n) i j)
      ≡⟨⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j ++ all-k-length-paths-from-to (suc n) (suc n) i j)
      ≈⟨ foldr-map (all-≤k-length-paths-from-to (suc n) n i j ++ all-k-length-paths-from-to (suc n) (suc n) i j) (weight m) ⟩
    foldr _+_ 0# (map (weight m) (all-≤k-length-paths-from-to (suc n) n i j ++ all-k-length-paths-from-to (suc n) (suc n) i j))
      ≡⟨ ≡-cong (foldr _+_ 0#) (map-++-commute (weight m) (all-≤k-length-paths-from-to (suc n) n i j) (all-k-length-paths-from-to (suc n) (suc n) i j)) ⟩
    foldr _+_ 0# ((map (weight m) (all-≤k-length-paths-from-to (suc n) n i j)) ++ (map (weight m) (all-k-length-paths-from-to (suc n) (suc n) i j)))
      ≈⟨ foldr-++-commute (map (weight m) (all-≤k-length-paths-from-to (suc n) n i j)) (map (weight m) (all-k-length-paths-from-to (suc n) (suc n) i j)) ⟩
    foldr _+_ 0# (map (weight m) (all-≤k-length-paths-from-to (suc n) n i j)) + foldr _+_ 0# (map (weight m) (all-k-length-paths-from-to (suc n) (suc n) i j))
      ≈⟨ +-cong (sym (foldr-map (all-≤k-length-paths-from-to (suc n) n i j) (weight m)))
                (sym (foldr-map (all-k-length-paths-from-to (suc n) (suc n) i j) (weight m))) ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j) + best-path-weight m (all-k-length-paths-from-to (suc n) (suc n) i j)
      ≈⟨ best-path-weight-lemma n i j 0stab m ⟩
    best-path-weight m (all-≤k-length-paths-from-to (suc n) n i j)
      ≈⟨ sym (mat-pow-sums-find-best-paths (suc n) n i j m) ⟩
    powSum 𝕄 m n i j ∎
  where open import Relation.Binary.EqReasoning setoid
        open import RoutingLib.db716.Data.List.Properties.MonoidFolds +-monoid
        𝕄 = SemiringMat (suc (suc n'))
