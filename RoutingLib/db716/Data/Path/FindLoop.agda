
module RoutingLib.db716.Data.Path.FindLoop where

open import Data.Fin using (Fin; _<_; _<?_) renaming (suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; ≤∧≢⇒<)
open import Data.List using (List ; _∷_; []; length; zip; lookup)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡) renaming (refl to ≈ₚ-refl)
open import Data.Nat using (ℕ; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; <-trans; n≤1+n; ≰⇒>)
open import Data.Product using (proj₁; proj₂; _,_; _×_; ∃; ∃₂)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)

open import RoutingLib.db716.Data.Path.UncertifiedFinite
open import RoutingLib.db716.Data.Path.VertexList
open import RoutingLib.db716.Data.Path.UncertifiedFinite.Properties

findLoopInVertexList : {n : ℕ} (p : List (Fin n)) → (suc n) ≤ length p → ∃₂ λ i j → i ≢ j × lookup p i ≡ lookup p j
findLoopInVertexList {n} p n+1≤|p| = pigeonhole n+1≤|p| (lookup p)

sortPair : ∀ {a} {n} {A : Set a} {f : Fin n → A} → (i j : Fin n) → i ≢ j → f i ≡ f j → ∃₂ λ i j → i < j × f i ≡ f j
sortPair i j i≢j f[i]≡f[j] with i <? j
... | yes i<j = i , j , i<j , f[i]≡f[j]
... | no i≰j = j , i , (≰⇒> λ i≤j → i≰j (≤∧≢⇒< i≤j i≢j)) , (sym f[i]≡f[j])

{-
-- Modified version of Data.List.Any.index which retains the proof of P (lookup xs i)
indexCertified : ∀ {a p} {A : Set a} {P : A → Set p} {xs} → Any P xs → ∃ λ i → P (lookup xs i)
indexCertified (here px) = Fin.zero , px
indexCertified (there pxs) =
  let (i , pxs[i]) = indexCertified pxs
  in Fin.suc i , pxs[i]-}

vertexLoop→edgeLoop : ∀ {n : ℕ} {l : List (Vertex n)} (i j : Fin (length l)) → i < j → lookup l i ≡ lookup l j → HasLoop ( fromVertexList l)
vertexLoop→edgeLoop {suc n} {x ∷ y ∷ l} Fin.zero (fsuc Fin.zero) 0<1 l[0]≡l[1] rewrite l[0]≡l[1] = trivial
vertexLoop→edgeLoop {suc n} {x ∷ y ∷ l} Fin.zero (fsuc (fsuc j)) 0<2+j x≡l[j] =
  let (z , [z,x]∈zip) = zip-∈ʳ (y ∷ l) (l) x (n≤1+n _) (Data.List.Relation.Unary.Any.map (λ l[j]≡? → trans x≡l[j] l[j]≡?) (∈-lookup j))
  in here {suc n} {fromVertexList (y ∷ l)} {z} {x} {y} [z,x]∈zip
  where
    zip-∈ʳ : ∀ {a} {A : Set a} (xs ys : List A) (y : A) → length ys ≤ length xs → y ∈ ys → ∃ λ x → (x , y) ∈ (zip xs ys)
    zip-∈ʳ (x₀ ∷ xs) (y₀ ∷ ys) (y) ys≤xs (here y≡y₀) rewrite y≡y₀ = x₀ , here refl
    zip-∈ʳ (x₀ ∷ xs) (y₀ ∷ ys) (y)(s≤s ys≤xs) (there y∈ys) =
      let x , [x,y]∈zip = zip-∈ʳ xs ys y ys≤xs y∈ys
      in x , there ([x,y]∈zip)
vertexLoop→edgeLoop {suc n} {x ∷ y ∷ l} (fsuc i) (fsuc j) (s≤s i<j) l[i]≡l[j] = there (vertexLoop→edgeLoop {l = y ∷ l} i j i<j l[i]≡l[j])

findLoop : {n : ℕ} {p : Path (suc n)} → ValidPath p → (suc n) ≤ length p → HasLoop p
findLoop {n} {x ∷ p} pIsValid n≤|p| rewrite (cong (HasLoop) (sym (from-toVertexList-≡ pIsValid))) = vertexLoop→edgeLoop {l = vertices} i' j' i'<j' p[i']≡p[j']
  where
    vertices = toVertexList (x ∷ p)

    lem0 : ∀ {k} (xs : Path (suc n)) → (suc k) ≤ length xs → (suc (suc k)) ≤ length (toVertexList xs)
    lem0 {k} (x ∷ xs) k≤|xs| rewrite (length-toVertexList xs x) = s≤s k≤|xs|
    
    loop : ∃₂ λ i j → i ≢ j × lookup (toVertexList (x ∷ p)) i ≡ lookup (toVertexList (x ∷ p)) j
    loop = findLoopInVertexList vertices (lem0 (x ∷ p) n≤|p|)

    i = proj₁ loop
    j = proj₁ (proj₂ loop)
    i≢j = proj₁ (proj₂ (proj₂ loop))
    p[i]≡p[j] = proj₂ (proj₂ (proj₂ loop))

    sorted : ∃₂ λ i j → i < j × lookup vertices i ≡ lookup vertices j
    sorted = sortPair i j i≢j p[i]≡p[j]
    i' = proj₁ sorted
    j' = proj₁ (proj₂ sorted)
    i'<j' = proj₁ (proj₂ (proj₂ sorted))
    p[i']≡p[j'] = proj₂ (proj₂ (proj₂ sorted))


long-paths-have-loops : ∀ {n} {k} {i j : Fin n} (xs : Path n) → n ≤ k → xs ∈ all-k-length-paths-from-to n k i j → HasLoop xs
long-paths-have-loops {suc n} {k} {i} {j} xs n≤k xs∈paths =
  let xs-valid : ValidPath xs
      xs-valid =  k-length-paths-valid k xs i j xs∈paths
      |xs|≡k : length xs ≡ k
      |xs|≡k = k-length-paths-length k xs i j xs∈paths
  in findLoop xs-valid (≤∧≡⇒≤ n≤k |xs|≡k)
  where open import Data.Nat.Properties using (≤-irrelevance)
        ≤∧≡⇒≤ : ∀ {a b c : ℕ} → a ≤ b → c ≡ b → a ≤ c
        ≤∧≡⇒≤ a≤b c≡b rewrite c≡b = a≤b
